use core::{
    fmt::{Debug, Formatter, Pointer},
    marker::PhantomData,
    ops::Deref,
};

use crate::{error::PackedPtrError, Packable, TypedPackedPtr};

#[repr(transparent)]
pub struct PackedRef<'a, T, D: Packable>(TypedPackedPtr<T, D>, PhantomData<&'a T>);

impl<'a, T, D: Packable> PackedRef<'a, T, D> {
    pub fn new(ptr: &'a T, data: D) -> Result<Self, PackedPtrError> {
        Ok(Self(TypedPackedPtr::new(ptr, data)?, PhantomData))
    }

    fn r#ref(self) -> &'a T {
        // SAFETY: the pointer is always valid per type invariant.
        unsafe { &*self.0.ptr() }
    }

    pub fn data(self) -> D {
        self.0.data()
    }

    pub fn get(self) -> (&'a T, D) {
        (self.r#ref(), self.0.data())
    }
}

impl<T, D: Packable> Deref for PackedRef<'_, T, D> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.r#ref()
    }
}

impl<T, D: Packable> Clone for PackedRef<'_, T, D> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, D: Packable> Copy for PackedRef<'_, T, D> {}

impl<T: Debug, D: Packable + Debug> Debug for PackedRef<'_, T, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("PackedRef")
            .field(&self.r#ref())
            .field(&self.data())
            .finish()
    }
}

impl<T, D: Packable> Pointer for PackedRef<'_, T, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        Pointer::fmt(&self.r#ref(), f)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new() {
        let data = 0xdeadbeefu32;
        let packed = 255u8;

        let ok = PackedRef::new(&data, packed).unwrap();

        assert_eq!(*ok, data);
        assert_eq!(ok.data(), packed);
        assert_eq!(ok.get(), (&data, packed));

        let packed = 255u32;
        let overflow = PackedRef::new(&data, packed);

        assert!(overflow.is_err());
        assert!(matches!(
            overflow.unwrap_err(),
            PackedPtrError::DataOverflow
        ));
    }
}
