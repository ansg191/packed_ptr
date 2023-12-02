use core::{
    fmt::{Debug, Formatter, Pointer},
    marker::PhantomData,
    ops::Deref,
};

use crate::{config::PtrCfg, error::PackedPtrError, Packable, TypedPackedPtr};

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

    fn r#ref(self) -> &'a T {
        // SAFETY: the pointer is always valid per type invariant.
        unsafe { &*self.0.ptr() }
    }

    #[must_use]
    pub fn data(self) -> D {
        self.0.data()
    }

    #[must_use]
    pub fn get(self) -> (&'a T, D) {
        (self.r#ref(), self.0.data())
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
}
