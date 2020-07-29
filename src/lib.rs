#![allow(incomplete_features)]
#![feature(const_generics)]
#![feature(coerce_unsized, unsize)]
#![deny(clippy::pedantic)]
#![no_std]

use core::any::type_name;
use core::any::Any;
use core::borrow::{Borrow, BorrowMut};
use core::marker::Unsize;
use core::mem::{align_of, forget, size_of, ManuallyDrop};
use core::ops::{CoerceUnsized, Deref, DerefMut};
use core::ptr;

pub type EmptyBox<T> = FixedBox<T, 0>;
pub type TinyBox<T> = FixedBox<T, 8>;
pub type SmallBox<T> = FixedBox<T, 64>;

pub struct FixedBox<T: ?Sized, const N: usize> {
    _align: [u64; 0],
    contents: [u8; N],
    fake_ptr: *const T,
}

impl<T, const N: usize> FixedBox<T, N> {
    #[must_use]
    pub fn new(t: T) -> Self {
        assert!(
            size_of::<T>() <= N,
            "The size of type `{}` ({} bytes) is larger than the FixedBox size ({} bytes).",
            type_name::<T>(),
            size_of::<T>(),
            N
        );

        let mut newbox: ManuallyDrop<FixedBox<T, N>> = ManuallyDrop::new(FixedBox {
            _align: [],
            fake_ptr: align_of::<T>() as *const T,
            contents: [0; N],
        });

        unsafe {
            // Write `t` into `contents`
            ptr::write(newbox.contents.as_mut_ptr() as *mut T, t);
        }

        ManuallyDrop::into_inner(newbox)
    }

    /// Try to box the given `t`, or return it back in an `Err` if the box is too small.
    //
    /// # Errors
    ///
    /// Will return `Err` if `t` is too small to fit in the given `FixedBox`.
    pub fn try_new(t: T) -> Result<Self, T> {
        if size_of::<T>() <= N {
            Ok(Self::new(t))
        } else {
            Err(t)
        }
    }

    #[must_use]
    pub fn resize<const M: usize>(self) -> FixedBox<T, M> {
        assert!(
            size_of::<T>() <= M,
            "The size of {} ({} bytes) is larger than resized FixedBox ({} bytes).",
            type_name::<T>(),
            size_of::<T>(),
            N
        );

        let mut newbox = ManuallyDrop::new(FixedBox {
            _align: [],
            fake_ptr: self.fake_ptr,
            contents: [0; M],
        });

        if M < N {
            // This is a resize down.
            newbox.contents.copy_from_slice(&self.contents[0..M]);
        } else {
            // This is a resize up.
            newbox.contents[0..N].copy_from_slice(&self.contents);
        }

        // We should forget `self` before grabbing the contents of `newbox`.
        // That ensures that if we panic somewhere in between, then we won't
        // ever drop two copies of the contained object.
        forget(self);
        ManuallyDrop::into_inner(newbox)
    }
}

impl<T: ?Sized, const N: usize> FixedBox<T, N> {
    #[must_use]
    pub fn resize_up<const M: usize>(self) -> FixedBox<T, M> {
        assert!(
            M >= N,
            "Must use `FixedBox::resize()` to make a FixedBox smaller."
        );

        let mut newbox = ManuallyDrop::new(FixedBox {
            _align: [],
            fake_ptr: self.fake_ptr,
            contents: [0; M],
        });

        newbox.contents[0..N].copy_from_slice(&self.contents);

        forget(self);
        ManuallyDrop::into_inner(newbox)
    }
}

impl<T: ?Sized + Unsize<U>, U: ?Sized, const N: usize> CoerceUnsized<FixedBox<U, N>>
    for FixedBox<T, N>
{
}

impl<T: ?Sized, const N: usize> Drop for FixedBox<T, N> {
    fn drop(&mut self) {
        unsafe { ptr::drop_in_place(&mut **self as *mut T) }
    }
}

impl<const N: usize> FixedBox<dyn Any + 'static, N> {
    /// Try downcasting a `FixedBox<dyn Any>` into concrete subtype.
    ///
    /// # Errors
    ///
    /// Will return self back as `Err` if the boxed value is not type `T`.
    pub fn downcast<T: 'static>(self) -> Result<FixedBox<T, N>, Self> {
        if (*self).is::<T>() {
            let mut newbox = ManuallyDrop::new(FixedBox {
                _align: [],
                fake_ptr: align_of::<T>() as *const T,
                contents: [0; N],
            });

            newbox.contents.copy_from_slice(&self.contents);
            forget(self);
            Ok(ManuallyDrop::into_inner(newbox))
        } else {
            Err(self)
        }
    }
}

impl<T: ?Sized, const N: usize> Deref for FixedBox<T, N> {
    type Target = T;

    fn deref(&self) -> &T {
        // A pointer is either thin or fat.
        // If it's thin, then it'll occupy one usize.
        // If it's fat, then it'll occupy two.
        let mut pointer: [usize; 2] = [0, 0];

        unsafe {
            // Copy either 8 or 16 bytes of pointer, depending on if T is fat.
            // The purpose of this is that pointer[1] will contain the vtable
            // or size, if needed.
            ptr::copy(
                &self.fake_ptr as *const *const T as *const usize,
                pointer.as_mut_ptr(),
                size_of::<*const T>() / size_of::<usize>(),
            );

            // Patch up the "pointer" to point to the actual object
            pointer[0] = self.contents.as_ptr() as usize;

            &*ptr::read(pointer.as_ptr() as *const *const T)
        }
    }
}

impl<T: ?Sized, const N: usize> DerefMut for FixedBox<T, N> {
    // Essentially a code duplicate of Deref.
    fn deref_mut(&mut self) -> &mut T {
        let mut pointer: [usize; 2] = [0, 0];
        unsafe {
            ptr::copy(
                &self.fake_ptr as *const *const T as *const usize,
                pointer.as_mut_ptr(),
                size_of::<*const T>() / size_of::<usize>(),
            );
            pointer[0] = self.contents.as_ptr() as usize;
            &mut *ptr::read(pointer.as_ptr() as *const *mut T)
        }
    }
}

impl<T: ?Sized, const N: usize> AsRef<T> for FixedBox<T, N> {
    fn as_ref(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized, const N: usize> AsMut<T> for FixedBox<T, N> {
    fn as_mut(&mut self) -> &mut T {
        &mut **self
    }
}

impl<T: ?Sized, const N: usize> Borrow<T> for FixedBox<T, N> {
    fn borrow(&self) -> &T {
        &**self
    }
}

impl<T: ?Sized, const N: usize> BorrowMut<T> for FixedBox<T, N> {
    fn borrow_mut(&mut self) -> &mut T {
        &mut **self
    }
}

impl<T: Clone, const N: usize> Clone for FixedBox<T, N> {
    fn clone(&self) -> Self {
        FixedBox::new((**self).clone())
    }
}

impl<T: core::fmt::Debug + ?Sized, const N: usize> core::fmt::Debug for FixedBox<T, N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        (**self).fmt(f)
    }
}

impl<T: core::fmt::Debug + ?Sized, const N: usize> core::fmt::Display for FixedBox<T, N> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        (**self).fmt(f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_slice() {
        let f: FixedBox<[u8], 5> = FixedBox::new([1, 2, 3, 4, 5]);
        let sum: u8 = f.iter().sum();

        assert_eq!(f.len(), 5);
        assert_eq!(sum, 15);
    }

    #[test]
    fn test_dyn() {
        let f: EmptyBox<dyn Fn() -> u8> = FixedBox::new(|| 100);
        assert_eq!(f(), 100);
    }

    #[test]
    fn test_downcast() {
        use core::any::Any;

        let f: SmallBox<dyn Any> = FixedBox::new(12345u64);
        let casted: Result<SmallBox<u64>, _> = f.downcast();

        assert!(casted.is_ok());
        assert_eq!(*casted.unwrap(), 12345u64);

        let f: SmallBox<dyn Any> = FixedBox::new(12345u64);
        let casted: Result<SmallBox<i16>, _> = f.downcast();

        assert!(casted.is_err());
    }

    #[test]
    fn test_too_small() {
        let f: Result<FixedBox<[u8; 4], 3>, [u8; 4]> = FixedBox::try_new([1, 2, 3, 4]);

        assert!(f.is_err());
    }

    #[test]
    fn test_just_right() {
        let f: Result<FixedBox<[u8; 4], 4>, [u8; 4]> = FixedBox::try_new([1, 2, 3, 4]);

        assert!(f.is_ok());
    }
}
