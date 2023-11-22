use core::fmt::{Debug, Display, Formatter};

/// Error type for [`PackedPtr::new`] & [`TypedPackedPtr::new`].
///
/// [`PackedPtr::new`]: crate::PackedPtr::new
/// [`TypedPackedPtr::new`]: crate::TypedPackedPtr::new
#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum PackedPtrError {
    /// The address is not aligned to the required alignment.
    UnalignedAddress,
    /// The data is too large to pack into the pointer.
    DataOverflow,
}

impl Display for PackedPtrError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        match *self {
            Self::UnalignedAddress => f.write_str("unaligned address"),
            Self::DataOverflow => f.write_str("data too large"),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for PackedPtrError {}
