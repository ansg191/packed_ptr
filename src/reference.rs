use core::{
    fmt::{Debug, Formatter, Pointer},
    marker::PhantomData,
    ops::Deref,
};

use crate::{config::PtrCfg, error::PackedPtrError, Packable, TypedPackedPtr};

/// A type safe reference to a packed pointer.
///
/// Equivalent to `&T` where `T` is the type of the pointer.
#[repr(transparent)]
pub struct PackedRef<'a, T, C: PtrCfg, D: Packable>(TypedPackedPtr<T, C, D>, PhantomData<&'a T>);

impl<'a, T, C: PtrCfg, D: Packable> PackedRef<'a, T, C, D> {
    /// Creates a new [`PackedRef`] from a reference and some data.
    ///
    /// # Errors
    ///
    /// * [`PackedPtrError::DataOverflow`] if the data is too large to fit in the pointer.
    /// * [`PackedPtrError::UnsafeConfig`] if the pointer is not compatible with the configuration.
    pub fn new(ptr: &'a T, data: D, cfg: C) -> Result<Self, PackedPtrError> {
        Ok(Self(TypedPackedPtr::new(ptr, data, cfg)?, PhantomData))
    }

    /// Creates a new [`PackedRef`] from a reference and some data without performing any safety
    /// checks.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the caller assumes the responsibility of ensuring that the
    /// provided `ptr` and `data` are valid and that they are compatible with the configuration.
    ///
    /// References are always aligned, therefore `ptr` should always be valid, but if the `ptr` of
    /// the system is incompatible with the configuration, then the reference will be corrupted,
    /// resulting in UB.
    ///
    /// Also, if the `data` is too big to fit in the pointer, undefined behavior may occur.
    ///
    /// # Arguments
    ///
    /// - `ptr`: A reference to a `T`
    /// - `data`: The data to be packed into the pointer.
    ///
    /// # Returns
    ///
    /// A new [`PackedRef`] with the given `ptr` and `data`.
    pub unsafe fn new_unchecked(ptr: &'a T, data: D) -> Self {
        Self(TypedPackedPtr::new_unchecked(ptr, data), PhantomData)
    }

    /// Returns the reference to the data.
    fn r#ref(self) -> &'a T {
        // SAFETY: the pointer is always valid per type invariant.
        unsafe { &*self.0.ptr() }
    }

    /// Returns the packed data value of the Packed Pointer.
    #[must_use]
    pub fn data(self) -> D {
        self.0.data()
    }

    /// Returns a tuple containing the reference and the packed data value.
    #[must_use]
    pub fn get(self) -> (&'a T, D) {
        (self.r#ref(), self.0.data())
    }

    /// Sets the packed data value of the pointer.
    ///
    /// # Arguments
    ///
    /// * `data`: The data to pack into the pointer.
    pub fn set_data(&mut self, data: D) {
        self.0.set_data(data);
    }
}

impl<T, C: PtrCfg, D: Packable> Deref for PackedRef<'_, T, C, D> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.r#ref()
    }
}

impl<T, C: PtrCfg, D: Packable> Clone for PackedRef<'_, T, C, D> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, C: PtrCfg, D: Packable> Copy for PackedRef<'_, T, C, D> {}

impl<T: Debug, C: PtrCfg, D: Packable + Debug> Debug for PackedRef<'_, T, C, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("PackedRef")
            .field(&self.r#ref())
            .field(&self.data())
            .finish()
    }
}

impl<T, C: PtrCfg, D: Packable> Pointer for PackedRef<'_, T, C, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        Pointer::fmt(&self.r#ref(), f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::AlignOnly;

    #[test]
    fn new() {
        let data = 0xdead_beef_u32;
        let packed = (true, false);

        let ok = PackedRef::new(&data, packed, AlignOnly).unwrap();

        assert_eq!(*ok, data);
        assert_eq!(ok.data(), packed);
        assert_eq!(ok.get(), (&data, packed));

        let packed = 255u32;
        let overflow = PackedRef::new(&data, packed, AlignOnly);

        assert!(overflow.is_err());
        assert!(matches!(
            overflow.unwrap_err(),
            PackedPtrError::DataOverflow
        ));
    }

    #[test]
    fn set_data() {
        let data = 0xdead_beef_u32;
        let packed = (true, false);

        let mut ref1 = PackedRef::new(&data, packed, AlignOnly).unwrap();

        assert_eq!(*ref1, data);
        assert_eq!(ref1.data(), packed);
        assert_eq!(ref1.get(), (&data, packed));

        let new_packed = (false, true);
        ref1.set_data(new_packed);

        assert_eq!(*ref1, data);
        assert_eq!(ref1.data(), new_packed);
        assert_eq!(ref1.get(), (&data, new_packed));
    }
}
