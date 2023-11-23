use sptr::Strict;

use crate::PackedPtrError;

/// A packed pointer that wraps a raw pointer to a specified type with additional data packed into
/// the pointer itself.
///
/// A [`PackedPtr`] will always be the same size as a raw pointer, but can contain a platform
/// specific amount of additional data.
///
/// On `ARMv8` the pointer will contain 16 + `log2(align_of::<T>)` bits of additional data:
/// - 16 bits are the most significant bits of the pointer. `ARMv8` requires that these bits are
///   either all 0 or all 1. On Windows, linux, and macOS the OS reserves all 1s for the kernel.
/// - `log2(align_of::<T>)` bits are the least significant bits of the pointer. Since pointers to
///   various types must be aligned to a specific number of bytes, we can use the lsb to store some
///   data. For example, if `T` is `u64` then the pointer must be aligned to 8 bytes, so we can use
///   the lsb to store 3 bits of data.
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
pub struct PackedPtr<T>(*const T);

impl<T> PackedPtr<T> {
    /// The size of a pointer in bytes.
    const PTR_SIZE: usize = core::mem::size_of::<usize>();
    /// The size of a pointer in bits.
    const PTR_SIZE_BITS: usize = Self::PTR_SIZE * 8;

    /// Types must be aligned to a specific number of bytes. This gives us some lsb to play with.
    const ALIGNMENT: usize = core::mem::align_of::<T>();
    const ALIGN_BITS: usize = Self::ALIGNMENT.trailing_zeros() as usize;
    const ALIGN_MASK: usize = Self::ALIGNMENT - 1;

    /// `ARMv8` specifies that the upper 16 bits of a pointer must be all 0 or all 1.
    /// That gives us 16 bits to store whatever we want.
    const MSB_BITS: usize = 16;
    const MSB_MASK: usize = !0 << (Self::PTR_SIZE_BITS - Self::MSB_BITS);

    /// The total number of free bits we can store in a pointer.
    ///
    /// Data stored in the pointer must be less than `2^Self::BITS`.
    pub const BITS: usize = Self::MSB_BITS + Self::ALIGN_BITS;

    pub const fn bits() -> usize {
        Self::BITS
    }
}

impl<T> PackedPtr<T> {
    /// Create a new packed pointer.
    ///
    /// Performs checks to ensure that the pointer is aligned and that the data will fit inside the
    /// free space available in the pointer.
    ///
    /// The data will fit in the pointer if & only if `data < 2^Self::BITS`.
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
    ///
    /// # Examples
    ///
    /// ```
    /// use packed_ptr::PackedPtr;
    ///
    /// let data = 0xdeadbeefu32;
    /// let ptr = PackedPtr::new(&data, 255).unwrap();
    /// assert_eq!(data, unsafe { *ptr.ptr() });
    /// assert_eq!(255, ptr.data());
    /// ```
    pub fn new(ptr: *const T, data: usize) -> Result<Self, PackedPtrError> {
        if Strict::addr(ptr) & Self::ALIGN_MASK != 0 {
            return Err(PackedPtrError::UnalignedAddress);
        }

        if data >= 1 << Self::BITS {
            return Err(PackedPtrError::DataOverflow);
        }

        // SAFETY: We have already checked that the pointer is aligned and that the data will fit in
        // the pointer.
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
    pub unsafe fn new_unchecked(ptr: *const T, data: usize) -> Self {
        let trunc_data = data & ((1 << Self::BITS) - 1);
        let upper = (trunc_data << (Self::PTR_SIZE_BITS - Self::BITS)) & Self::MSB_MASK;
        let lower = trunc_data & Self::ALIGN_MASK;

        let ptr = Strict::map_addr(ptr, |addr| addr | upper | lower);
        Self(ptr)
    }

    /// Retrieves a pointer to the data stored in the structure along with the data.
    ///
    /// # Returns
    ///
    /// Returns a tuple containing a pointer to the data and the length of the data.
    ///
    /// The `*const T` is a raw pointer to the data stored in the structure, while the `usize` represents the length of the data.
    pub fn get(self) -> (*const T, usize) {
        let ptr = self.ptr();
        let data = self.data();
        (ptr, data)
    }

    /// Returns a raw pointer to the underlying data.
    ///
    /// This method calculates the address of the underlying data by masking out the most significant bit (`Self::MSB_MASK`)
    /// and the alignment bits (`Self::ALIGN_MASK`). It then returns the resulting pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use packed_ptr::PackedPtr;
    ///
    /// let data = 0xdeadbeefu32;
    /// let ptr = PackedPtr::new(&data, 255).unwrap();
    /// assert_eq!(data, unsafe { *ptr.ptr() });
    /// ```
    pub fn ptr(self) -> *const T {
        Strict::map_addr(self.0, |addr| addr & !Self::MSB_MASK & !Self::ALIGN_MASK)
    }

    /// Extracts the data from the packed pointer.
    ///
    /// Data will be a value in the range `0..2^Self::BITS`.
    ///
    /// # Returns
    ///
    /// The extracted data as a `usize` value.
    ///
    /// # Example
    ///
    /// ```
    /// use packed_ptr::PackedPtr;
    ///
    /// let value = 0x12345678;
    /// let ptr = PackedPtr::new(&value, 255).unwrap();
    /// assert_eq!(255, ptr.data());
    /// ```
    pub fn data(self) -> usize {
        let addr = Strict::addr(self.0);
        let upper = addr & Self::MSB_MASK;
        let lower = addr & Self::ALIGN_MASK;
        (upper >> (Self::PTR_SIZE_BITS - Self::BITS)) | lower
    }
}

super::impl_ptr!(PackedPtr);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bits() {
        assert_eq!(PackedPtr::<u8>::BITS, 16);
        assert_eq!(PackedPtr::<u16>::BITS, 17);
        assert_eq!(PackedPtr::<u32>::BITS, 18);
        assert_eq!(PackedPtr::<u64>::BITS, 19);
        assert_eq!(PackedPtr::<u128>::BITS, 20);
    }

    #[test]
    fn round_trip() {
        let data = 0xdeadbeefu32;
        let packed = 255;

        let ptr = PackedPtr::new(&data, packed).unwrap();

        assert_eq!(data, unsafe { *ptr.ptr() });
        assert_eq!(packed, ptr.data());
    }

    #[test]
    fn new() {
        let data = 0xdeadbeefu32;

        let overflow = PackedPtr::new(&data, 1 << 18);
        assert!(matches!(overflow, Err(PackedPtrError::DataOverflow)));

        let ok = PackedPtr::new(&data, (1 << 18) - 1);
        assert!(matches!(ok, Ok(_)));
    }

    #[test]
    fn eq() {
        let data = 0xdeadbeefu32;
        let ptr = PackedPtr::new(&data, 255).unwrap();
        let ptr2 = PackedPtr::new(&data, 255).unwrap();
        assert_eq!(ptr, ptr2);

        let ptr3 = PackedPtr::new(&data, 254).unwrap();
        assert_ne!(ptr, ptr3);

        let data2 = 0xdeadbeefu32;
        let ptr4 = PackedPtr::new(&data2, 255).unwrap();
        assert_ne!(ptr, ptr4);
    }
}
