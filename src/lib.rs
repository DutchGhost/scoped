//! This crate provides little utilities to declare callbacks inside a scope,
//! that get executed on success, failure, or exit on that scope.
//!
//! This is different than the ScopeGuard crate does,
//! because here it's dependent on the scope's outcome which callbacks should run.
use std::{
    cell::RefCell,
    ops::{Deref, DerefMut},
};

trait Defer {
    fn call(self: Box<Self>);
}

impl<F: FnMut(T), T> Defer for DeferCallback<T, F> {
    fn call(mut self: Box<Self>) {
        if let Some(item) = self.item {
            (self.call_fn)(item);
        }
    }
}

#[derive(Debug)]
struct DeferCallback<T, F> {
    item: Option<T>,
    call_fn: F,
}

impl<T, F> DeferCallback<T, F> {
    const fn new(item: T, call_fn: F) -> Self {
        Self {
            item: Some(item),
            call_fn,
        }
    }
}

#[derive(Default)]
pub struct DeferStack<'a> {
    inner: RefCell<Vec<Box<dyn Defer + 'a>>>,
}

unsafe fn extend_lifetime_mut<'a, 'b, T: ?Sized>(x: &'a mut T) -> &'b mut T {
    std::mem::transmute(x)
}

impl<'a> DeferStack<'a> {

    fn push<'s, T: 'a>(&'s self, item: T, closure: impl FnMut(T) + 'a) -> Handle<'a, T> {
        let mut deferred = Box::new(DeferCallback::new(item, closure));

        // This operation is safe,
        // We create a mutable reference to the item of the deferred closure,
        // and extend its lifetime, so it can be returned.
        //
        // Extending the lifetime is safe here,
        // because `deferred` is stored on the heap.
        // Moving the box (as we do with .push()) does not invalidate the mutable reference,
        // and we never touch the box again without &mut self
        let ret = unsafe { extend_lifetime_mut(&mut deferred.item) };
        self.inner.borrow_mut().push(deferred);
        Handle { inner: ret }
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
pub struct Handle<'a, T> {
    inner: &'a mut Option<T>,
}

impl<'a, T> Handle<'a, T> {
    /// Cancel's the handle's deferred closure,
    /// returning the value the closure was going to be called with.
    #[inline]
    pub fn cancel(self) -> T {
        self.inner.take().expect("Called cancel on an empty Handle")
    }
}

impl<'a, T> Deref for Handle<'a, T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner
            .as_ref()
            .expect("Called deref on an empty Handle")
    }
}

impl<'a, T> DerefMut for Handle<'a, T> {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.inner
            .as_mut()
            .expect("Called deref_mut on an empty Handle")
    }
}

/// A guard is a handle to schedule closures on.
/// Scheduling a closure takes a closure with 1 parameter,
/// and the parameter it is going to be called with.
/// It returns a [`Handle`] to the parameter, so it's still usable within the scope.
/// A [`Handle`] implements Deref and DerefMut, to access the parameter.
/// To cancel a callback, [`Handle::cancel`] should be called.
///
/// Its important to note that closures scheduled with [`Guard::on_scope_exit`] will *always* run,
/// and will always run after all closures scheduled to run on success or failure are executed.
///
/// The last scheduled closure gets runned first.
#[derive(Default)]
pub struct Guard<'a> {
    /// Callbacks to be run on a scope's success.
    on_scope_success: DeferStack<'a>,

    /// Callbacks to be run on a scope's failure.
    on_scope_failure: DeferStack<'a>,

    /// Callbacks to be run on a scope's exit.
    on_scope_exit: DeferStack<'a>,
}

impl<'a> Guard<'a> {
    /// Schedules defered closure `dc` to run on a scope's success.
    /// The deferred closure can be cancelled using [`Handle::cancel`],
    /// returning the value the closure was going to be called with.
    #[allow(clippy::mut_from_ref)]
    pub fn on_scope_success<'s, T: 'a>(&'s self, item: T, dc: impl FnMut(T) + 'a) -> Handle<T> {
        self.on_scope_success.push(item, dc)
    }

    /// Schedules defered closure `dc` to run on a scope's exit.
    /// The deferred closure can be cancelled using [`Handle::cancel`],
    /// returning the value the closure was going to be called with.
    #[allow(clippy::mut_from_ref)]
    pub fn on_scope_exit<'s, T: 'a>(&'s self, item: T, dc: impl FnMut(T) + 'a) -> Handle<T> {
        self.on_scope_exit.push(item, dc)
    }

    /// Schedules defered closure `dc` to run on a scope's failure.
    /// The deferred closure can be cancelled using [`Handle::cancel`],
    /// returning the value the closure was going to be called with.
    #[allow(clippy::mut_from_ref)]
    pub fn on_scope_failure<'s, T: 'a>(&'s self, item: T, dc: impl FnMut(T) + 'a) -> Handle<T> {
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
pub fn scoped<'a, R: Failure>(scope: impl FnOnce(&mut Guard<'a>) -> R) -> R {
    let mut guard = Guard::default();

    let ret = scope(&mut guard);

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
        let scope = scoped(|guard| {
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

            Some(10)
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
}
