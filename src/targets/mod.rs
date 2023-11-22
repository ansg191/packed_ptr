use crate::PackedPtrError;

cfg_if::cfg_if! {
    if #[cfg(target_arch = "aarch64")] {
        #[path = "armv8.rs"] mod imp;
    } else if #[cfg(target_arch = "x86_64")] {
        #[path = "x86_64.rs"] mod imp;
    } else {
        #[path = "fallback.rs"] mod imp;
    }
}

#[repr(transparent)]
pub struct PackedPtr<T>(imp::PackedPtr<T>);

impl<T> PackedPtr<T> {
    /// The total number of free bits we can store in a pointer.
    ///
    /// Data stored in the pointer must be less than `2^Self::BITS`.
    pub fn bits() -> usize {
        imp::PackedPtr::<T>::bits()
    }

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
        imp::PackedPtr::new(ptr, data).map(Self)
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
        Self(imp::PackedPtr::new_unchecked(ptr, data))
    }

    /// Retrieves a pointer to the data stored in the structure along with the data.
    ///
    /// # Returns
    ///
    /// Returns a tuple containing a pointer to the data and the length of the data.
    ///
    /// The `*const T` is a raw pointer to the data stored in the structure, while the `usize` represents the length of the data.
    pub fn get(self) -> (*const T, usize) {
        self.0.get()
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
        self.0.ptr()
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
        self.0.data()
    }
}

impl<T> From<&T> for PackedPtr<T> {
    fn from(value: &T) -> Self {
        // SAFETY: references are always aligned.
        unsafe { Self::new_unchecked(value, 0) }
    }
}

impl<T> TryFrom<*const T> for PackedPtr<T> {
    type Error = PackedPtrError;

    fn try_from(value: *const T) -> Result<Self, Self::Error> {
        Self::new(value, 0)
    }
}

impl<T> TryFrom<(*const T, usize)> for PackedPtr<T> {
    type Error = PackedPtrError;

    fn try_from(value: (*const T, usize)) -> Result<Self, Self::Error> {
        Self::new(value.0, value.1)
    }
}

impl<T> From<PackedPtr<T>> for *const T {
    fn from(value: PackedPtr<T>) -> Self {
        value.ptr()
    }
}

macro_rules! impl_ptr {
    ($p:ident) => {
        impl<T> core::fmt::Debug for $p<T> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.debug_tuple(stringify!($p))
                    .field(&self.ptr())
                    .field(&self.data())
                    .finish()
            }
        }

        impl<T> core::fmt::Pointer for $p<T> {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                core::fmt::Pointer::fmt(&self.ptr(), f)
            }
        }

        impl<T> Copy for $p<T> {}

        impl<T> Clone for $p<T> {
            fn clone(&self) -> Self {
                *self
            }
        }

        impl<T> PartialEq for $p<T> {
            fn eq(&self, other: &Self) -> bool {
                self.get() == other.get()
            }
        }

        impl<T> Eq for $p<T> {}

        impl<T> core::hash::Hash for $p<T> {
            fn hash<H: core::hash::Hasher>(&self, state: &mut H) {
                self.get().hash(state)
            }
        }
    };
}
pub(crate) use impl_ptr;

impl_ptr!(PackedPtr);
