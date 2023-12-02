use core::{marker::PhantomData, mem::size_of};

use sptr::Strict;

use crate::{
    config::{PtrCfg, PtrCfgExt},
    PackedPtrError,
};

const PTR_SIZE_BITS: usize = size_of::<*const ()>() * 8;

/// A packed pointer that wraps a raw pointer to a specified type with additional data packed into
/// the pointer itself.
///
/// A [`PackedPtr`] will always be the same size as a raw pointer, but can contain a configuration
/// specific amount of data packed into the pointer itself.
///
/// # Safety
///
/// Creating a `PackedPtr` instance requires a raw pointer, which can be obtained from other safe or
/// unsafe operations. It's important to ensure the safety of the source of the raw pointer when
/// using `PackedPtr`, as it does not provide additional checks or guarantees like Rust's reference
/// lifetimes do.
///
/// This struct does not enforce any guarantees about the validity or ownership of the pointed-to
/// data. It is the responsibility of the user to ensure that the underlying data remains valid and
/// accessible for the lifetime of this pointer.
///
/// With that being said, `PackedPtr` does provide some safety requirements:
/// - The pointer must be aligned to the alignment of `T`.
/// - The data must be less than `2^Self::BITS`.
#[repr(transparent)]
pub struct PackedPtr<T, C: PtrCfg>(*const T, PhantomData<C>);

impl<T, C: PtrCfg> PackedPtr<T, C> {
    /// The number of bits available for storing data in the pointer.
    /// Equivalent to [`C::bits::<T>()`](PtrCfg::bits).
    #[must_use]
    pub fn bits() -> usize {
        C::bits::<T>()
    }

    /// Create a new packed pointer.
    ///
    /// Performs checks to ensure that the pointer is aligned and that the data will fit inside the
    /// free space available in the pointer.
    ///
    /// The data will fit in the pointer if & only if `data < 2^C::bits()`.
    ///
    /// See [`PtrCfg`] for more information on how to configure the number of bits available for
    /// storing data.
    ///
    /// # Arguments
    ///
    /// * `ptr`: Pointer to data to pack.
    /// * `data`: Data to pack into the pointer.
    ///
    /// returns: `Result<PackedPtr<T>, NewPackedPtrError>`
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
    /// use packed_ptr::PackedPtr;
    /// use packed_ptr::config::AlignOnly;
    ///
    /// let data = 0xdeadbeefu32;
    /// let ptr = PackedPtr::new(&data, 1, AlignOnly).unwrap();
    /// assert_eq!(data, unsafe { *ptr.ptr() });
    /// assert_eq!(1, ptr.data());
    /// ```
    #[allow(clippy::not_unsafe_ptr_arg_deref, clippy::needless_pass_by_value)]
    pub fn new(ptr: *const T, data: usize, _cfg: C) -> Result<Self, PackedPtrError> {
        if Strict::addr(ptr) & C::lsb_bits_mask::<T>() != 0 {
            return Err(PackedPtrError::UnalignedAddress);
        }

        if data >= 1 << Self::bits() {
            return Err(PackedPtrError::DataOverflow);
        }

        if !C::check_ptr(ptr) {
            return Err(PackedPtrError::UnsafeConfig);
        }

        // SAFETY: We just checked that the address is aligned and that the data will fit in the
        // pointer.
        Ok(unsafe { Self::new_unchecked(ptr, data) })
    }

    /// Create a new packed pointer without performing any checks.
    ///
    /// If the pointer is not aligned the resulting packed pointer will be invalid.
    /// If the data is too large the data will be truncated to fit in the pointer.
    ///
    /// # Arguments
    ///
    /// * `ptr`: Pointer to data to pack.
    /// * `data`: Data to pack into the pointer.
    ///
    /// returns: `PackedPtr<T>`
    ///
    /// # Safety
    ///
    /// This function is unsafe because it does not perform any checks to ensure that the pointer is
    /// properly aligned or that the data will fit in the pointer.
    ///
    /// Passing an unaligned pointer will cause the pointer to be truncated to the nearest aligned
    /// address.
    ///
    /// Passing data that is too large will cause the data to be truncated to fit in the pointer.
    ///
    /// Passing a pointer that is not compatible with the configuration will cause the pointer to be
    /// corrupted, leading to UB.
    pub unsafe fn new_unchecked(ptr: *const T, data: usize) -> Self {
        let trunc_data = data & ((1 << Self::bits()) - 1);
        let upper = (trunc_data << (PTR_SIZE_BITS - Self::bits())) & C::msb_bits_mask();
        let lower = trunc_data & C::lsb_bits_mask::<T>();

        let ptr = Strict::map_addr(ptr, |addr| addr | upper | lower);
        Self(ptr, PhantomData)
    }

    /// Retrieves a pointer to the data stored in the structure along with the data.
    ///
    /// # Returns
    ///
    /// Returns a tuple containing a pointer to the data and the length of the data.
    ///
    /// The `*const T` is a raw pointer to the data stored in the structure, while the `usize` represents the length of the data.
    #[must_use]
    pub fn get(self) -> (*const T, usize) {
        let ptr = self.ptr();
        let data = self.data();
        (ptr, data)
    }

    /// Returns a raw pointer to the underlying data.
    ///
    /// This method calculates the address of the underlying data by masking out the most significant bit
    /// and the alignment bits. It then returns the resulting pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use packed_ptr::PackedPtr;
    /// use packed_ptr::config::AlignOnly;
    ///
    /// let data = 0xdeadbeefu32;
    /// let ptr = PackedPtr::new(&data, 1, AlignOnly).unwrap();
    /// assert_eq!(data, unsafe { *ptr.ptr() });
    /// ```
    #[must_use]
    pub fn ptr(self) -> *const T {
        Strict::map_addr(self.0, |addr| {
            addr & !C::msb_bits_mask() & !C::lsb_bits_mask::<T>()
        })
    }

    /// Extracts the data from the packed pointer.
    ///
    /// Data will be a value in the range `0..2^Self::bits()`.
    ///
    /// # Returns
    ///
    /// The extracted data as a `usize` value.
    ///
    /// # Example
    ///
    /// ```
    /// use packed_ptr::PackedPtr;
    /// use packed_ptr::config::AlignOnly;
    ///
    /// let value = 0x12345678;
    /// let ptr = PackedPtr::new(&value, 1, AlignOnly).unwrap();
    /// assert_eq!(1, ptr.data());
    /// ```
    #[must_use]
    pub fn data(self) -> usize {
        let addr = Strict::addr(self.0);
        let upper = addr & C::msb_bits_mask();
        let lower = addr & C::lsb_bits_mask::<T>();
        (upper >> (PTR_SIZE_BITS - Self::bits())) | lower
    }
}

impl<T, C: PtrCfg> core::fmt::Debug for PackedPtr<T, C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        f.debug_tuple("PackedPtr")
            .field(&self.ptr())
            .field(&self.data())
            .finish()
    }
}

impl<T, C: PtrCfg> core::fmt::Pointer for PackedPtr<T, C> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        core::fmt::Pointer::fmt(&self.ptr(), f)
    }
}

impl<T, C: PtrCfg> Copy for PackedPtr<T, C> {}

impl<T, C: PtrCfg> Clone for PackedPtr<T, C> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T, C: PtrCfg> PartialEq for PackedPtr<T, C> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl<T, C: PtrCfg> Eq for PackedPtr<T, C> {}

impl<T, C: PtrCfg> core::hash::Hash for PackedPtr<T, C> {
    fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
        self.get().hash(state);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::config::AlignOnly;

    #[test]
    fn round_trip() {
        let data = 0xdead_beef_u32;
        let packed = 2;

        let ptr = PackedPtr::new(&data, packed, AlignOnly).unwrap();

        assert_eq!(data, unsafe { *ptr.ptr() });
        assert_eq!(packed, ptr.data());
    }

    #[test]
    fn new() {
        let data = 0xdead_beef_u32;

        let overflow = PackedPtr::new(&data, 4, AlignOnly);
        assert!(matches!(overflow, Err(PackedPtrError::DataOverflow)));

        let ok = PackedPtr::new(&data, 3, AlignOnly);
        assert!(ok.is_ok());
    }

    #[test]
    fn eq() {
        let data = 0xdead_beef_u32;
        let ptr = PackedPtr::new(&data, 2, AlignOnly).unwrap();
        let ptr2 = PackedPtr::new(&data, 2, AlignOnly).unwrap();
        assert_eq!(ptr, ptr2);

        let ptr3 = PackedPtr::new(&data, 1, AlignOnly).unwrap();
        assert_ne!(ptr, ptr3);

        let data2 = 0xdead_beef_u32;
        let ptr4 = PackedPtr::new(&data2, 2, AlignOnly).unwrap();
        assert_ne!(ptr, ptr4);
    }
}
