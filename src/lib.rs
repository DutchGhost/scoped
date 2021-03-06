//! This crate provides little utilities to declare callbacks inside a scope,
//! that get executed on success, failure, or exit on that scope.
//!
//! This is different than the ScopeGuard crate does,
//! because here it's dependent on the scope's outcome which callbacks should run.
use std::{
    cell::UnsafeCell,
    ops::{Deref, DerefMut},
};

#[derive(Debug)]
struct Callback<T, F> {
    item: T,
    call_fn: F,
}

impl<T, F> Callback<T, F> {
    const fn new(item: T, call_fn: F) -> Self {
        Self { item, call_fn }
    }
}

#[derive(Debug)]
enum DeferCallBack<T, F> {
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

struct DeferStack<'a> {
    inner: UnsafeCell<Vec<*mut (dyn Defer + 'a)>>,
}

impl <'a> Drop for DeferStack<'a> {
    fn drop(&mut self) {
        unsafe {
            let v: &mut Vec<_> = &mut *(self.inner.get());

            for defer in v.drain(..).map(|ptr| Box::from_raw(ptr)) {
                drop(defer);
            }
        }
    }
}

impl<'a> DeferStack<'a> {
    #[inline]
    fn new() -> Self {
        Self {
            inner: UnsafeCell::new(Vec::new()),
        }
    }

    fn push_with<'s, T: 'a, F: FnOnce(T) + 'a>(&'s self, item: T, closure: F) -> Handle<'s, T, F> {
        let deferred = Box::new(DeferCallBack::Scheduled(Callback::new(item, closure)));

        // The Box is transformed into a raw pointer,
        // then the raw pointer *itself* is copied, an transformed into a mutable reference,
        // and then the original raw pointer is transformed back into a box,
        // finally the mutable reference is returned in the form of a Handle.
        //
        // This is safe, because the Handle has lifetime 's, which is the lifetime of Self.
        // Trying to hold onto a Handle when Self drops, is not possible.
        //
        // Also, the Handle is not invalidad whenever the Box moves (on a vectors reallocation for example),
        // because the mutable reference the Handle contains, references heap memory.
        unsafe {
            let raw_ptr = Box::into_raw(deferred);

            let ret: &mut DeferCallBack<T, F> = &mut *raw_ptr;
            let deferred = raw_ptr;

            (&mut *(self.inner.get())).push(deferred);

            Handle { inner: ret }
        }
    }

    fn push<'s, F: FnOnce() + 'a>(&'s self, closure: F) -> Handle<'s, (), impl FnOnce(())> {
        self.push_with((), |_| closure())
    }

    fn execute(mut self) {
        let v = std::mem::replace(&mut self.inner, UnsafeCell::new(vec![]));
        for defer in v.into_inner().into_iter().rev().map(|ptr| unsafe {
            Box::from_raw(ptr)
        }) {    
            defer.call();
        }
    }
}

/// A handle is a handle back to a deferred closure.
/// In order to cancel the closure, and get back the value the closure was going to be called with,
/// use [`Handle::cancel`].
pub struct Handle<'a, T, F> {
    inner: &'a mut DeferCallBack<T, F>,
}

impl<'a, T, F> Handle<'a, T, F> {
    /// Cancel's the handle's deferred closure,
    /// returning the value the closure was going to be called with.
    #[inline]
    pub fn cancel(self) -> T {
        // drop the function, return the value
        let Callback { item, .. } = self.inner.take().expect("Called cancel on an empty Handle");

        item
    }
}

impl<'a, T, F> Deref for Handle<'a, T, F> {
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

impl<'a, T, F> DerefMut for Handle<'a, T, F> {
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
///
/// A guard can schedule 2 closure types,
/// closures that take no arguments,
/// and closures that take 1 argument.
///
/// Scheduling a closure that takes no arguments, can be done trough the following methods:
/// - [`Guard::on_scope_success`]
/// - [`Guard::on_scope_failure`]
/// - [`Guard::on_scope_exit`]
///
/// These methods return a [`Handle`], through which cancelling of the scheduled closure is possible.
///
/// Scheduling a closure that takes 1 argument, can be done trough the following methods:
/// - [`Guard::on_scope_success_with`]
/// - [`Guard::on_scope_failure_with`]
/// - [`Guard::on_scope_exit_with`]
///
/// These methods also take the argument they are going to be called with, and return a [`Handle`].
/// The [`Handle`] can be used to cancel the scheduled closure, as well as accessing the given argument trough [`Deref`] and [`DerefMut`]
///
/// Its important to note that closures scheduled with [`Guard::on_scope_exit`] and [`Guard::on_scope_exit_with`], will *always* run,
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
    pub fn on_scope_success<'s, F: FnOnce() + 'a>(
        &'s self,
        dc: F,
    ) -> Handle<'s, (), impl FnOnce(()) + 'a> {
        self.on_scope_success.push(dc)
    }

    /// Schedules deferred closure `dc` to run on a scope's exit.
    /// The deferred closure can be cancelled using [`Handle::cancel`],
    pub fn on_scope_exit<'s, F: FnOnce() + 'a>(&'s self, dc: F) -> Handle<'s, (), impl FnOnce(())> {
        self.on_scope_exit.push(dc)
    }

    /// Schedules deferred closure `dc` to run on a scope's failure.
    /// The deferred closure can be cancelled using [`Handle::cancel`],
    pub fn on_scope_failure<'s, F: FnOnce() + 'a>(
        &'s self,
        dc: F,
    ) -> Handle<'s, (), impl FnOnce(())> {
        self.on_scope_failure.push(dc)
    }

    /// Schedules deferred closure `dc` to run on a scope's exit.
    /// The deferred closure can be cancelled using [`Handle::cancel`],
    /// returning the value the closure was going to be called with.
    pub fn on_scope_exit_with<'s, T: 'a, F: FnOnce(T) + 'a>(
        &'s self,
        item: T,
        dc: F,
    ) -> Handle<'s, T, F> {
        self.on_scope_exit.push_with(item, dc)
    }

    /// Schedules deferred closure `dc` to run on a scope's failure.
    /// The deferred closure can be cancelled using [`Handle::cancel`],
    /// returning the value the closure was going to be called with.
    pub fn on_scope_failure_with<'s, T: 'a, F: FnOnce(T) + 'a>(
        &'s self,
        item: T,
        dc: F,
    ) -> Handle<'s, T, F> {
        self.on_scope_failure.push_with(item, dc)
    }

    /// Schedules deferred closure `dc` to run on a scope's success.
    /// The deferred closure can be cancelled using [`Handle::cancel`],
    /// returning the value the closure was going to be called with.
    pub fn on_scope_success_with<'s, T: 'a, F: FnOnce(T) + 'a>(
        &'s self,
        item: T,
        dc: F,
    ) -> Handle<'s, T, F> {
        self.on_scope_success.push_with(item, dc)
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
/// A guard is used to schedule callbacks to run on a scope's success, failure, or exit.
///
/// For more information on how to use the guard, see [`Guard`].
///
/// The scope is required to return a type implementing [`Failure`],
/// to indicate whether the scoped exited with success, or failure.
///
/// # Examples
/// ```
/// use scoped::{Guard, scoped};
///
/// fn main() {
///     use std::cell::Cell;
///
///     let mut n = Cell::new(0);
///
///     scoped(|guard| -> Result<(), ()> {
///
///         guard.on_scope_exit(|| {
///             assert_eq!(n.get(), 2);
///             n.set(3);
///         });
///
///         guard.on_scope_success(|| {
///             assert_eq!(n.get(), 1);
///             n.set(2);
///         });
///
///         n.set(1);
///         Ok(())
///     });
///     assert_eq!(n.get(), 3);
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
///         let mut handle = guard.on_scope_exit_with(&mut v, |vec| {
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
pub fn scoped<'a, R: Failure>(scope: impl FnOnce(&Guard<'a>) -> R + 'a) -> R {
    // Notice that only an &Guard<'a> is given,
    // this way, 2 guard's can never be mem::swap`d,
    // or mem::replace`d.

    let guard = Guard {
        on_scope_success: DeferStack::new(),
        on_scope_failure: DeferStack::new(),
        on_scope_exit: DeferStack::new(),
    };

    let ret = scope(&guard);

    if !ret.is_error() {
        guard.on_scope_success.execute();
    } else {
        guard.on_scope_failure.execute();
    }

    guard.on_scope_exit.execute();

    ret
}

pub type ScopeResult<E> = Result<(), E>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_list() {
        let mut v = vec![1, 2, 3, 4, 5];
        scoped(|guard| -> Option<()> {
            let mut v = guard.on_scope_success_with(&mut v, |v| {
                println!("SUCCES!");

                assert_eq!(*v, vec![1, 2, 3, 4, 5, 6, 7]);

                v.push(10);
            });

            let mut boxed = guard.on_scope_exit_with(Box::new(1), move |boxed| {
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

            guard.on_scope_success_with(&number, move |b| {
                assert!(2 == b.get());
                b.set(0);
            });

            guard.on_scope_failure_with(&number, move |b| {
                b.set(-1);
            });

            guard.on_scope_exit_with(&number, move |b| {
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
            let mut v = guard.on_scope_exit_with(v, |vec| panic!(vec));

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
    //         let handle = guard.on_scope_exit_with(vec![1, 2, 3, 4], |v| {});

    //         handles.push(handle);

    //         Some(())
    //     });
    // }

    // #[test]
    // fn test_swap_guards() {
    //     scoped(|good_guard| {
    //         let mut g = good_guard.on_scope_success_with(vec![0], |mut v| {
    //             assert!(v == vec![0]);
    //         });

    //         g.extend(0..2000);

    //         scoped(|bad_guard| -> Option<()> {

    //             std::mem::swap(good_guard, bad_guard);

    //             None
    //         });

    //         let x = &*g;

    //         Some(())
    //     });
    // }

    // #[test]
    // fn test_cell_swap() {
    //     use std::cell::Cell;

    //     scoped(|guard| {
    //         let mut v = guard.on_scope_success_with(vec![1, 2, 3, 4], |v| {});

    //         let mut c1 = Cell::new(guard);

    //         scoped(|evil_guard| {
    //             let mut c2 = Cell::new(evil_guard);

    //             c2.swap(&c1);

    //             Some(())
    //         });

    //         v.push(10);

    //         Some(())
    //     });
    // }
}
