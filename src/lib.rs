#![allow(incomplete_features)]
#![feature(const_generics)]
#![feature(coerce_unsized, unsize)]
#![deny(clippy::pedantic)]
#![no_std]

use core::{
    any::{type_name, Any},
    borrow::{Borrow, BorrowMut},
    marker::Unsize,
    mem::{align_of, forget, size_of, ManuallyDrop},
    ops::{CoerceUnsized, Deref, DerefMut},
    ptr,
};

pub type EmptyBox<T> = FixedBox<T, 0>;
pub type TinyBox<T> = FixedBox<T, 8>;
pub type SmallBox<T> = FixedBox<T, 64>;

pub struct FixedBox<T: ?Sized, const N: usize> {
    /// This is a "phantom"-ish pointer that allows us to implement the
    /// CoerceUnsized trait. When we promote this from a T:Sized to a T:Unsized,
    /// this pointer becomes a fat pointer and we can then use it to grab the
    /// vtable/other info. Thanks Rust for letting us do this.
    fake_ptr: *const T,
    // Align the object to 64-bits. This is "probably" sufficient.
    _align: [u64; 0],
    /// This actually holds the object we care about.
    contents: [u8; N],
}

impl<T, const N: usize> FixedBox<T, N> {
    /// Construct a `FixedBox<T, N>` from a value of type `T`.
    ///
    /// # Panics
    ///
    /// Panics if the size of `T` is smaller than our box size `N`.
    #[must_use]
    pub fn new(t: T) -> Self {
        assert!(
            size_of::<T>() <= N,
            "The size of type `{}` ({} bytes) is larger \
            than the FixedBox size ({} bytes).",
            type_name::<T>(),
            size_of::<T>(),
            N
        );

        // TODO(compiler-errors): Is it safe to initialize the FixedBox like
        // this, because the only unsafe action we can perform on this object
        // would be to `Deref<Target=T>` it or drop it...
        let mut newbox: ManuallyDrop<FixedBox<T, N>> = ManuallyDrop::new(FixedBox {
            fake_ptr: align_of::<T>() as *const T,
            _align: [],
            contents: [0; N],
        });

        // Write our contents `t` into the box. This also ensures `t` won't
        // get dropped, since this function consumes it.
        unsafe {
            ptr::write(newbox.contents.as_mut_ptr() as *mut T, t);
        }

        // Finally, we can unwrap the box. From now on, it can be used without
        // worries.
        ManuallyDrop::into_inner(newbox)
    }

    /// Try to box the given `t`, or return it back in an `Err` if the box is
    /// too small.
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
    /// Resize a box. Can be either smaller or larger, but must be large enough
    /// to hold the contents of the box.
    ///
    /// # Panics
    ///
    /// Panics if the new box size `M` is too small to hold the sized type `T`.
    pub fn resize<const M: usize>(self) -> FixedBox<T, M> {
        assert!(
            size_of::<T>() <= M,
            "The size of contents `{}` ({} bytes) is too small for resized \
            FixedBox ({} bytes).",
            type_name::<T>(),
            size_of::<T>(),
            N
        );

        let mut newbox = ManuallyDrop::new(FixedBox {
            fake_ptr: self.fake_ptr,
            _align: [],
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
        // That ensures that if we panic somewhere in this method, then we won't
        // ever drop two copies of the boxed object.
        forget(self);
        ManuallyDrop::into_inner(newbox)
    }

    /// Try to resize a box, or return it back in an `Err` if the new size is
    /// too small.
    //
    /// # Errors
    ///
    /// Will return self as `Err` if contents are too small to fit in the
    /// new `FixedBox`.
    pub fn try_resize<const M: usize>(self) -> Result<FixedBox<T, M>, Self> {
        if size_of::<T>() <= M {
            Ok(self.resize())
        } else {
            Err(self)
        }
    }
}

impl<T: ?Sized, const N: usize> FixedBox<T, N> {
    /// Resize a box that contains an unsized type. Since the type is unsized
    /// and we have no information about the size of the contained object,
    /// we can only make the box larger.
    ///
    /// # Panics
    ///
    /// Panics if the new box size `M` is smaller than the box size `N`.
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

impl<T: ?Sized, const N: usize> Drop for FixedBox<T, N> {
    fn drop(&mut self) {
        // Drop the contents of the box. This takes advantage of the DerefMut
        // impl, which does the heavy lifting to reinterpret the pointer
        // agnostic to its being fat or thin.
        unsafe { ptr::drop_in_place(&mut **self as *mut T) }
    }
}

/* Here's where the magic happens. Because we implement this, we get to
 * take advantage of `FixedBox<dyn Trait, _>` for free!
 */
impl<T: ?Sized + Unsize<U>, U: ?Sized, const N: usize> CoerceUnsized<FixedBox<U, N>>
    for FixedBox<T, N>
{
}

impl<T: ?Sized, const N: usize> Deref for FixedBox<T, N> {
    type Target = T;

    fn deref(&self) -> &T {
        // TODO(compiler-errors): Is this an assumption we can only make on x86?
        // A pointer is either thin or fat.
        // If it's thin, then it'll occupy one usize.
        // If it's fat, then it'll occupy two.
        assert!(
            size_of::<*const T>() == size_of::<usize>()
                || size_of::<*const T>() == 2 * size_of::<usize>()
        );

        let mut pointer: [usize; 2] = [0, 0];

        unsafe {
            // Copy either 1 or 2 "usizes" of pointer, depending on if T is fat.
            // The purpose of this is that pointer[1] will contain the vtable
            // or size, if needed. pointer[0] actually just contains the
            // alignment, which we don't really care about...
            ptr::copy(
                &self.fake_ptr as *const *const T as *const usize,
                pointer.as_mut_ptr(),
                size_of::<*const T>() / size_of::<usize>(),
            );

            // Patch up the "pointer" to point to the actual object.
            // This is hacky and makes me sad, but it works.
            pointer[0] = self.contents.as_ptr() as usize;

            // Reinterpret the `pointer` usize array as a `*const T`.
            &*ptr::read(pointer.as_ptr() as *const *const T)
        }
    }
}

impl<T: ?Sized, const N: usize> DerefMut for FixedBox<T, N> {
    // Essentially a code duplicate of the Deref impl.
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

impl<const N: usize> FixedBox<dyn Any + 'static, N> {
    /// Try downcasting a `FixedBox<dyn Any>` into concrete subtype.
    ///
    /// # Errors
    ///
    /// Will return self back as `Err` if the boxed value is not type `T`.
    pub fn downcast<T: 'static>(self) -> Result<FixedBox<T, N>, Self> {
        if (*self).is::<T>() {
            // Basically just make a new `FixedBox<T>`...
            let mut newbox = ManuallyDrop::new(FixedBox {
                _align: [],
                fake_ptr: align_of::<T>() as *const T,
                contents: [0; N],
            });

            // Copy full "contents" slice.
            newbox.contents.copy_from_slice(&self.contents);

            // We need to forget `self` so we don't accidentally call the
            // drop method of the contained contents.
            forget(self);

            // Now let's unwrap and return the newbox.
            Ok(ManuallyDrop::into_inner(newbox))
        } else {
            Err(self)
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

// TODO(compiler-errors): I should also do impls for Hash, Eq, Ord,
// PartialEq, PartialOrd, etc.

#[cfg(test)]
#[macro_use]
extern crate std;

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

        let f: TinyBox<u64> = TinyBox::new(130u64);
        let k: Result<FixedBox<u64, 0>, TinyBox<u64>> = f.try_resize();
        assert!(k.is_err());
    }

    #[test]
    fn test_just_right() {
        let f: Result<FixedBox<[u8; 4], 4>, [u8; 4]> = FixedBox::try_new([1, 2, 3, 4]);
        assert!(f.is_ok());
    }

    #[test]
    fn test_resize() {
        let f: SmallBox<u64> = SmallBox::new(12u64);
        let k: TinyBox<u64> = f.resize();
        assert_eq!(*k, 12u64);

        let f: SmallBox<u64> = SmallBox::new(12u64);
        let k: Result<EmptyBox<u64>, _> = f.try_resize();
        assert!(k.is_err());
    }

    #[test]
    fn test_dyn_fn() {
        use std::vec::Vec;

        fn return_three() -> i32 {
            3
        }

        struct Foo(i32, i32);
        let five = Foo(5, 0);

        let x: Vec<TinyBox<dyn Fn() -> i32>> = vec![
            TinyBox::new(return_three),
            TinyBox::new(|| 4),
            TinyBox::new(|| {
                let five = &five;
                five.0
            }),
        ];

        let mut sum = 0;
        for f in x {
            sum += f();
        }

        assert_eq!(sum, 3 + 4 + 5);
    }
}
