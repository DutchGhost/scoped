//! This crate provides little utilities to declare callbacks inside a scope,
//! that get executed on success, failure, or exit on that scope.
//!
//! This is different than the ScopeGuard crate does,
//! because here it's dependent on the scope's outcome which callbacks should run.
use std::{
    cell::RefCell,
    marker::PhantomData,
    ops::{Deref, DerefMut},
};

#[derive(Debug)]
pub struct Callback<T, F> {
    item: T,
    call_fn: F,
}

impl<T, F> Callback<T, F> {
    const fn new(item: T, call_fn: F) -> Self {
        Self { item, call_fn }
    }
}

#[derive(Debug)]
pub enum DeferCallBack<T, F> {
    Scheduled(Callback<T, F>),
    Cancelled,
}

impl<T, F> DeferCallBack<T, F> {
    fn as_ref(&self) -> Option<&Callback<T, F>> {
        match self {
            DeferCallBack::Scheduled(ref callback) => Some(callback),
            _ => None,
        }
    }

    fn as_mut(&mut self) -> Option<&mut Callback<T, F>> {
        match self {
            DeferCallBack::Scheduled(ref mut callback) => Some(callback),
            _ => None,
        }
    }

    fn take(&mut self) -> Option<Callback<T, F>> {
        match std::mem::replace(self, DeferCallBack::Cancelled) {
            DeferCallBack::Scheduled(callback) => Some(callback),
            _ => None,
        }
    }
}

trait Defer {
    fn call(self: Box<Self>);
}

impl<F: FnOnce(T), T> Defer for DeferCallBack<T, F> {
    fn call(self: Box<Self>) {
        if let DeferCallBack::Scheduled(callback) = *self {
            (callback.call_fn)(callback.item)
        }
    }
}

pub struct DeferStack<'a> {
    inner: RefCell<Vec<Box<dyn Defer + 'a>>>,
}

impl<'a> DeferStack<'a> {
    #[inline]
    fn new() -> Self {
        Self {
            inner: RefCell::new(Vec::new()),
        }
    }

    fn push<'s, T: 'a, F: FnOnce(T) + 'a>(&'s self, item: T, closure: F) -> Handle<'a, 's, T, F> {
        // This is used *carefully*,
        // and only used with a mutable reference to some heap allocated memory.
        unsafe fn extend_lifetime_mut<'a, 'b, T: ?Sized>(x: &'a mut T) -> &'b mut T {
            std::mem::transmute(x)
        }

        let mut deferred = Box::new(DeferCallBack::Scheduled(Callback::new(item, closure)));

        // This operation is safe,
        // We create a mutable reference to the item of the deferred closure,
        // and extend its lifetime, so it can be returned.
        //
        // Extending the lifetime is safe here,
        // because `deferred` is stored on the heap.
        // Moving the box (as we do with .push()) does not invalidate the mutable reference,
        // and we never touch the box again without &mut self
        let ret: &mut DeferCallBack<T, F> = unsafe { extend_lifetime_mut(&mut *deferred) };

        self.inner.borrow_mut().push(deferred);
        Handle {
            inner: ret,
            lifetime: PhantomData,
        }
    }

    fn execute(mut self) {
        let v = std::mem::replace(self.inner.get_mut(), vec![]);
        for d in v.into_iter().rev() {
            d.call();
        }
    }
}

/// A handle is a handle back to the value a deferred closure is going to be called with.
/// In order to cancel the closure, and get back the value, use [`Handle::cancel`].
pub struct Handle<'a, 'life, T, F> {
    inner: &'a mut DeferCallBack<T, F>,

    /// Ties back to the lifetime of the DeferStack,
    /// this prevents leaking a Handle into a vector of an outer scope.
    lifetime: PhantomData<&'life mut T>,
}

impl<'a, 's, T, F> Handle<'a, 's, T, F> {
    /// Cancel's the handle's deferred closure,
    /// returning the value the closure was going to be called with.
    #[inline]
    pub fn cancel(self) -> T {
        // drop the function, return the value
        let Callback { item, .. } = self.inner.take().expect("Called cancel on an empty Handle");

        item
    }
}

impl<'a, 's, T, F> Deref for Handle<'a, 's, T, F> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self
            .inner
            .as_ref()
            .expect("Called deref on an empty Handle")
            .item
    }
}

impl<'a, 's, T, F> DerefMut for Handle<'a, 's, T, F> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self
            .inner
            .as_mut()
            .expect("Called deref_mut on an empty Handle")
            .item
    }
}

/// A guard is a handle to schedule closures on.
/// Scheduling a closure takes a closure, and the paremeter to call it with.
/// The returned value from scheduling is a [`Handle`].
///
/// This handle implements Deref and DerefMut,
/// through which the specified parameter is still accesable within the scope.
///
/// Its important to note that closures scheduled with [`Guard::on_scope_exit`] will *always* run,
/// and will always run after all closures scheduled to run on success or failure are executed.
///
/// The last scheduled closure gets runned first.
pub struct Guard<'a> {
    /// Callbacks to be run on a scope's success.
    on_scope_success: DeferStack<'a>,

    /// Callbacks to be run on a scope's failure.
    on_scope_failure: DeferStack<'a>,

    /// Callbacks to be run on a scope's exit.
    on_scope_exit: DeferStack<'a>,
}

// @NOTE: A GUARD SHOULD ONLY BE CREATED BY THE LIBRARY.
// ANY WAY TO CREATE A GUARD AS A USER OF THIS LIBRARY IS UNSOUND,
// BECAUSE YOU COULD drop(mem::replace(old_guard, new_guard)),
// WHICH INVALIDATES ALL HANDLES RETURNED BY `old_guard`.
//
// THIS IS WHY THERE IS NO DEFAULT IMPLEMENTATION, OR EVEN A NEW METHOD.
impl<'a> Guard<'a> {
    /// Schedules deferred closure `dc` to run on a scope's success.
    /// The deferred closure can be cancelled using [`Handle::cancel`],
    /// returning the value the closure was going to be called with.
    pub fn on_scope_success<'s, T: 'a, F: FnOnce(T) + 'a>(
        &'s self,
        item: T,
        dc: F,
    ) -> Handle<'a, 's, T, F> {
        self.on_scope_success.push(item, dc)
    }

    /// Schedules deferred closure `dc` to run on a scope's exit.
    /// The deferred closure can be cancelled using [`Handle::cancel`],
    /// returning the value the closure was going to be called with.
    pub fn on_scope_exit<'s, T: 'a, F: FnOnce(T) + 'a>(
        &'s self,
        item: T,
        dc: F,
    ) -> Handle<'a, 's, T, F> {
        self.on_scope_exit.push(item, dc)
    }

    /// Schedules deferred closure `dc` to run on a scope's failure.
    /// The deferred closure can be cancelled using [`Handle::cancel`],
    /// returning the value the closure was going to be called with.
    pub fn on_scope_failure<'s, T: 'a, F: FnOnce(T) + 'a>(
        &'s self,
        item: T,
        dc: F,
    ) -> Handle<'a, 's, T, F> {
        self.on_scope_failure.push(item, dc)
    }
}

/// A trait to annotate whether a type is `success` or `failure`.
pub trait Failure {
    /// Returns true if the type is in a failure state, false otherwise.
    fn is_error(&self) -> bool;
}

impl<T, E> Failure for Result<T, E> {
    /// [`Result::Ok`] is success, [`Result::Err`] is failure.
    fn is_error(&self) -> bool {
        self.is_err()
    }
}

impl<T> Failure for Option<T> {
    /// [`Option::Some`] is success, [`Option::None`] is failure.
    fn is_error(&self) -> bool {
        self.is_none()
    }
}

/// Executes the scope `scope`.
/// A scope is a closure, in which access to a guard is granted.
/// A guard is used to schedule callbacks to run on a scope's success, failure, or exit, using
/// [`Guard::on_scope_success`], [`Guard::on_scope_failure`], [`Guard::on_scope_exit`].
///
/// # Examples
/// ```
/// use scoped::{Guard, scoped};
///
/// fn main() {
///     use std::cell::Cell;
///
///     let mut number = Cell::new(0);
///
///     scoped(|guard| -> Result<(), ()> {
///
///         guard.on_scope_exit(&number, move |n| {
///             assert_eq!(n.get(), 2);
///             n.set(3);
///         });
///
///         guard.on_scope_success(&number, move |n| {
///             assert_eq!(n.get(), 1);
///             n.set(2);
///         });
///
///         number.set(1);
///         Ok(())
///     });
///     assert_eq!(number.get(), 3);
/// }
/// ```
///
/// A callback can also be cancelled, using [`Handle::cancel`]
/// ```
/// use scoped::{Guard, scoped};
///
/// fn main() {
///
///     let mut v = vec![1, 2, 3];
///
///     scoped(|guard| -> Option<()> {
///         let mut handle = guard.on_scope_exit(&mut v, |vec| {
///             panic!()
///         });
///
///         handle.push(4);
///         
///         let cancelled = handle.cancel();
///
///         cancelled.push(5);
///         
///         Some(())
///     });
///
///     assert_eq!(v, vec![1, 2, 3, 4, 5]);
/// }
/// ```
pub fn scoped<'a, R: Failure>(scope: impl FnOnce(&mut Guard<'a>) -> R) -> R {
    let mut guard = Guard {
        on_scope_success: DeferStack::new(),
        on_scope_failure: DeferStack::new(),
        on_scope_exit: DeferStack::new(),
    };

    let ret = scope(&mut guard);

    if !ret.is_error() {
        guard.on_scope_success.execute();
    } else {
        guard.on_scope_failure.execute();
    }

    guard.on_scope_exit.execute();

    ret
}

#[macro_export]
macro_rules! scope_success {
    ($guard:expr, $capture:expr, $exec:expr) => {
        $guard.on_scope_success($capture, $exec)
    };

    ($guard:expr, $exec:expr) => {
        $guard.on_scope_success((), |_| $exec())
    };
}

#[macro_export]
macro_rules! scope_failure {
    ($guard:expr, $capture:expr, $exec:expr) => {
        $guard.on_scope_failure($capture, $exec)
    };

    ($guard:expr, $exec:expr) => {
        $guard.on_scope_failure((), |_| $exec())
    };
}

#[macro_export]
macro_rules! scope_exit {
    ($guard:expr, $capture:expr, $exec:expr) => {
        $guard.on_scope_exit($capture, $exec)
    };

    ($guard:expr, $exec:expr) => {
        $guard.on_scope_exit((), |_| $exec())
    };
}

pub type ScopeResult<E> = Result<(), E>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_list() {
        let mut v = vec![1, 2, 3, 4, 5];
        scoped(|guard| -> Option<()> {
            let mut v = guard.on_scope_success(&mut v, |v| {
                println!("SUCCES!");

                assert_eq!(*v, vec![1, 2, 3, 4, 5, 6, 7]);

                v.push(10);
            });

            let mut boxed = guard.on_scope_exit(Box::new(1), move |boxed| {
                assert_eq!(*boxed, 12);
            });

            v.push(6);
            v.push(7);

            **boxed = 12;

            Some(())
        });
    }

    #[test]
    fn main_test() {
        use std::cell::Cell;

        let number = Cell::new(0);

        let n = scoped(|guard| {
            let n = Some(1);

            guard.on_scope_success(&number, move |b| {
                assert!(2 == b.get());
                b.set(0);
            });

            guard.on_scope_failure(&number, move |b| {
                b.set(-1);
            });

            guard.on_scope_exit(&number, move |b| {
                b.set(0);
            });

            number.set(2);

            n
        });

        assert!(number.get() == 0);
        assert_eq!(n, Some(1));
    }

    #[test]
    fn test_cancell() {
        let v = vec![1, 2, 3, 4, 5];

        let v = scoped(|guard| -> Result<Vec<_>, ()> {
            let mut v = guard.on_scope_exit(v, |vec| panic!(vec));

            v.push(10);

            let v = v.cancel();

            Ok(v)
        });

        assert_eq!(v, Ok(vec![1, 2, 3, 4, 5, 10]));
    }

    // #[test]
    // fn leak_handle() {
    //     let mut handles = vec![];

    //     scoped(|guard| {
    //         let handle = guard.on_scope_exit(vec![1, 2, 3, 4], |v| {});

    //         handles.push(handle);

    //         Some(())
    //     });
    // }
}
