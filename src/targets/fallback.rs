use sptr::Strict;

use crate::PackedPtrError;

#[repr(transparent)]
pub struct PackedPtr<T>(*const T);

impl<T> PackedPtr<T> {
    const ALIGNMENT: usize = core::mem::align_of::<T>();
    const ALIGN_BITS: usize = Self::ALIGNMENT.trailing_zeros() as usize;
    const ALIGN_MASK: usize = Self::ALIGNMENT - 1;

    pub const BITS: usize = Self::ALIGN_BITS;

    pub fn bits() -> usize {
        Self::BITS
    }
}

impl<T> PackedPtr<T> {
    pub fn new(ptr: *const T, data: usize) -> Result<Self, PackedPtrError> {
        if Strict::addr(ptr) & Self::ALIGN_MASK != 0 {
            return Err(PackedPtrError::UnalignedAddress);
        }

        if data >= 1 << Self::BITS {
            return Err(PackedPtrError::DataOverflow);
        }

        // SAFETY: We just checked that the address is aligned and that the data will fit in the
        // pointer.
        Ok(unsafe { Self::new_unchecked(ptr, data) })
    }

    pub unsafe fn new_unchecked(ptr: *const T, data: usize) -> Self {
        let lower = data & Self::ALIGN_MASK;

        let ptr = Strict::map_addr(ptr, |addr| addr | lower);
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
        Strict::map_addr(self.0, |addr| addr & !Self::ALIGN_MASK)
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
        addr & Self::ALIGN_MASK
    }
}

super::impl_ptr!(PackedPtr);
