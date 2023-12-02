use core::{
    convert::TryFrom,
    fmt::{Debug, Formatter, Pointer},
    hash::Hash,
    marker::PhantomData,
};

use crate::{config::PtrCfg, error::PackedPtrError, Packable, PackedPtr};

/// A [`PackedPtr`] with a type-safe packed data value.
///
/// A `TypedPackedPtr` will always be the same size as a raw pointer, and can contain a
/// platform-specific amount of additional data. The amount of additional data is platform-specific,
/// and may be zero.
///
/// `D` must implement [`Packable`], which allows it to be packed into the pointer. [`Packable`] an
/// unsafe trait & requires [`Copy`]. See [`Packable`] for more information about its safety
/// requirements.
///
/// Because [`Packable`] is [`Copy`], `TypedPackedPtr` is [`Copy`] as well.
///
/// # Safety
///
/// A `TypedPackedPtr` is still a pointer, and has the same safety requirements as a raw pointer.
/// This struct does not enforce any guarantees about the validity or ownership of the pointed-to
/// data. It is the responsibility of the user to ensure that the underlying data remains valid and
/// accessible for the lifetime of this pointer.
///
/// Additionally, `TypedPackedPtr` has the same safety requirements as [`PackedPtr`]:
/// - The pointer must be aligned to the alignment of `T`.
/// - The packed data must be less than `2^Self::BITS`.
///
/// And also has its own safety requirements:
/// - `D` must adhere to the safety requirements of [`Packable`].
/// - Data packed into the pointer must be created from [`Packable::pack`].
/// - Data unpacked from the pointer must be retrieved via [`Packable::unpack`].
#[repr(transparent)]
pub struct TypedPackedPtr<T, C: PtrCfg, D: Packable>(PackedPtr<T, C>, PhantomData<D>);

impl<T, C: PtrCfg, D: Packable> TypedPackedPtr<T, C, D> {
    /// Create a new `TypedPackedPtr` with the given pointer and data.
    ///
    /// # Arguments
    ///
    /// * `ptr` - A raw pointer to the underlying data.
    /// * `data` - The data to be packed into the pointer.
    ///
    /// # Returns
    ///
    /// Returns a `Result` containing either the new `TypedPackedPtr` instance or an error
    /// if the data overflows the available bits for packing or the pointer is unaligned.
    ///
    /// # Errors
    ///
    /// * [`PackedPtrError::UnalignedAddress`]: The pointer is not aligned.
    /// * [`PackedPtrError::DataOverflow`]: The data will not fit in the pointer.
    /// * [`PackedPtrError::UnsafeConfig`]: The pointer is not compatible with the configuration.
    ///
    /// # Examples
    ///
    /// ```
    /// use packed_ptr::TypedPackedPtr;
    /// use packed_ptr::config::AlignOnly;
    ///
    /// let data = 0xdeadbeefu32;
    /// let packed = [true, false];
    /// let ptr = TypedPackedPtr::new(&data, packed, AlignOnly).unwrap();
    /// assert_eq!(data, unsafe { *ptr.ptr() });
    /// assert_eq!(packed, ptr.data());
    /// ```
    pub fn new(ptr: *const T, data: D, cfg: C) -> Result<Self, PackedPtrError> {
        if <D as Packable>::MAX_BITS > PackedPtr::<T, C>::bits() {
            return Err(PackedPtrError::DataOverflow);
        }

        let data = data.pack();
        let ptr = PackedPtr::new(ptr, data, cfg)?;
        Ok(Self(ptr, PhantomData))
    }

    /// Creates a new instance of `Self` without performing any safety checks.
    ///
    /// # Safety
    ///
    /// This function is unsafe because the caller assumes the responsibility of ensuring that the
    /// provided `ptr` and `data` are valid and that they are compatible with the configuration.
    ///
    /// If the provided `ptr` is a unaligned, or if the `data` is too big to fit in the pointer,
    /// undefined behavior may occur.
    ///
    /// If the `ptr` is incompatible with the configuration, then the `ptr` may be corrupted,
    /// resulting in UB.
    ///
    /// # Arguments
    ///
    /// - `ptr`: A raw pointer to the data of type `T`.
    /// - `data`: The data to be packed into the pointer.
    ///
    /// # Returns
    ///
    /// A new instance of `Self` with the given `ptr` and `data`.
    pub unsafe fn new_unchecked(ptr: *const T, data: D) -> Self {
        let data = data.pack();
        let ptr = PackedPtr::new_unchecked(ptr, data);
        Self(ptr, PhantomData)
    }

    /// Returns the raw pointer value of the Packed Pointer.
    #[must_use]
    pub fn ptr(self) -> *const T {
        self.get().0
    }

    /// Returns the packed data value of the Packed Pointer.
    #[must_use]
    pub fn data(self) -> D {
        self.get().1
    }

    /// Returns a tuple containing the raw pointer value and the packed data value.
    #[must_use]
    pub fn get(self) -> (*const T, D) {
        // SAFETY: The data is always valid because it is packed in `new`.
        (self.0.ptr(), unsafe { D::unpack(self.0.data()) })
    }

    /// Sets the packed data value of the pointer.
    ///
    /// # Arguments
    ///
    /// * `data`: The data to pack into the pointer.
    pub fn set_data(&mut self, data: D) {
        // SAFETY: ptr & config are valid since unchanged. Data is valid since type was checked in
        // `new`.
        *self = unsafe { Self::new_unchecked(self.ptr(), data) };
    }
}

impl<T, C: PtrCfg, D: Packable> Clone for TypedPackedPtr<T, C, D> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, C: PtrCfg, D: Packable> Copy for TypedPackedPtr<T, C, D> {}

impl<T, C: PtrCfg, D: Packable + Debug> Debug for TypedPackedPtr<T, C, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("TypedPackedPtr")
            .field(&self.ptr())
            .field(&self.data())
            .finish()
    }
}

impl<T, C: PtrCfg, D: Packable> Pointer for TypedPackedPtr<T, C, D> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        Pointer::fmt(&self.ptr(), f)
    }
}

impl<T, C: PtrCfg, D: Packable + PartialEq> PartialEq for TypedPackedPtr<T, C, D> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl<T, C: PtrCfg, D: Packable + Eq> Eq for TypedPackedPtr<T, C, D> {}

impl<T, C: PtrCfg, D: Packable + Hash> Hash for TypedPackedPtr<T, C, D> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.get().hash(state);
    }
}

impl<T, C: PtrCfg, D: Packable + Default> TryFrom<*const T> for TypedPackedPtr<T, C, D> {
    type Error = PackedPtrError;

    fn try_from(value: *const T) -> Result<Self, Self::Error> {
        Self::new(value, D::default(), C::default())
    }
}

impl<T, C: PtrCfg, D: Packable> TryFrom<(*const T, D)> for TypedPackedPtr<T, C, D> {
    type Error = PackedPtrError;

    fn try_from(value: (*const T, D)) -> Result<Self, Self::Error> {
        Self::new(value.0, value.1, C::default())
    }
}

impl<T, C: PtrCfg, D: Packable> From<TypedPackedPtr<T, C, D>> for *const T {
    fn from(value: TypedPackedPtr<T, C, D>) -> Self {
        value.ptr()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::AlignOnly;

    #[test]
    fn round_trip() {
        let data = 0xdead_beef_u32;
        let packed = (true, false);

        let ptr = TypedPackedPtr::new(&data, packed, AlignOnly).unwrap();

        assert_eq!(data, unsafe { *ptr.ptr() });
        assert_eq!(packed, ptr.data());
    }

    #[test]
    fn new() {
        let data = 0xdead_beef_u32;

        let packed = 5u32;
        let overflow = TypedPackedPtr::new(&data, packed, AlignOnly);
        assert!(overflow.is_err());
        assert!(matches!(
            overflow.unwrap_err(),
            PackedPtrError::DataOverflow
        ));

        let packed = true;
        let ok = TypedPackedPtr::new(&data, packed, AlignOnly);
        assert!(ok.is_ok());
    }

    #[test]
    fn array() {
        let data = 0xdead_beef_u32;
        let packed = [true, false];
        let ptr = TypedPackedPtr::new(&data, packed, AlignOnly).unwrap();
        assert_eq!(data, unsafe { *ptr.ptr() });
        assert_eq!(packed, ptr.data());
    }

    #[test]
    fn set_data() {
        let data = 0xdead_beef_u32;
        let packed = (true, false);
        let mut ptr = TypedPackedPtr::new(&data, packed, AlignOnly).unwrap();
        assert_eq!(data, unsafe { *ptr.ptr() });
        assert_eq!(packed, ptr.data());

        let new_packed = (false, true);
        ptr.set_data(new_packed);

        assert_eq!(data, unsafe { *ptr.ptr() });
        assert_eq!(new_packed, ptr.data());
    }
}
