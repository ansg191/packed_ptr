//! Configuration for [`PackedPtr`](crate::PackedPtr).
//!
//! All configurations must implement the [`PtrCfg`] trait.
//! This trait is sealed and cannot be implemented outside of this crate.
//!
//! There are 2 types of `PtrCfg`s that are available for all platforms:
//! * [`None`]: No data can be packed into the pointer.
//! * [`AlignOnly`]: Only the alignment of the pointer can be packed into the pointer.
//!
//! There are also platform-specific `PtrCfg`s that are available on some platforms.
//! For example on `x86_64`, there is [`Level4Paging`] & [`Level5Paging`] for 48-bit & 57-bit
//! addresses respectively.

use core::mem::align_of;

mod private {
    pub trait Sealed {}
}

/// A configuration for a [`PackedPtr`](crate::PackedPtr).
///
/// This trait is sealed and cannot be implemented outside of this crate.
/// Implementations are provided for various platforms.
///
/// There are 2 types of `PtrCfg`s that are available for all platforms:
/// * [`None`]: No data can be packed into the pointer.
///   This configuration will always fail when packing data into a pointer.
/// * [`AlignOnly`]: Only the alignment of the pointer can be packed into the pointer.
///   This configuration will use the alignment of a pointer to determine how many bits can be packed
///   into the LSBs of the pointer.
///
/// A pointer can pack data into 2 places in a pointer: the LSB bits & the MSB bits.
///
/// The LSB bits use the fact that data has a ABI-defined minimum alignment. That means pointers to
/// data must be a multiple of that alignment. For example, `u32` has a minimum alignment of 4, so
/// the last 2 bits of a pointer to a `u32` will always be 0. We can use those 2 bits to store data.
/// This method is safe as long as the pointer is aligned.
///
/// The MSB bits use the fact that 64-bit architectures don't actually use all 64 bits of a pointer.
/// For example, on `x86_64`, most CPUs only use the lower 48 bits of a pointer. Most ISA's specify
/// that the upper bits of a pointer must be all 0s or all 1s. And most OS's specify that the
/// address space of userspace processes must be in the lower half of the address space. We can use
/// these upper unused bits to store even more data in the pointer, as long as we return the pointer
/// back to all 0s before de-referencing it.
///
/// Of course, the amount of the MSB bits is platform-specific, OS-specific, and CPU-specific. So it
/// is the responsibility of the user to ensure that the pointer & config combination they use is
/// safe. However, we can perform checks at runtime to ensure that the provided pointer can be
/// safely converted into a `PackedPtr` with the provided config.
pub trait PtrCfg: private::Sealed + Default {
    /// The number of bits available for storing data in the LSBs of a pointer.
    /// May depend on the type of the pointer.
    #[must_use]
    fn lsb_bits<T>() -> usize;

    /// The number of bits available for storing data in the MSBs of a pointer.
    #[must_use]
    fn msb_bits() -> usize;

    /// The total number of bits available for storing data in a pointer.
    /// May depend on the type of the pointer.
    #[must_use]
    fn bits<T>() -> usize {
        Self::lsb_bits::<T>() + Self::msb_bits()
    }
}

macro_rules! ptr_cfg {
    (
        $(#[$outer:meta])*
        $(pub)* struct $cfg:ident($align:literal, $msb:literal);
    ) => {
        $(#[$outer])*
        pub struct $cfg;
        impl private::Sealed for $cfg {}
        impl PtrCfg for $cfg {
            fn lsb_bits<T>() -> usize {
                if $align {
                    align_of::<T>().trailing_zeros() as usize
                } else {
                    0
                }
            }
            fn msb_bits() -> usize {
                $msb
            }
        }
        impl Default for $cfg {
            fn default() -> Self { Self }
        }
    }
}

ptr_cfg! {
    /// 64-bit address
    ///
    /// Can pack no data into a pointer.
    pub struct None(false, 0);
}

ptr_cfg! {
    /// 64-bit address with alignment requirements
    ///
    /// Can pack [`align_of::<T>()`] bits of data into a pointer.
    pub struct AlignOnly(true, 0);
}

#[cfg(target_arch = "x86_64")]
ptr_cfg! {
    /// 57-bit address
    ///
    /// Can pack 7 + [`align_of::<T>()`] bits of data into a pointer.
    pub struct Level5Paging(true, 7);
}

#[cfg(target_arch = "x86_64")]
ptr_cfg! {
    /// 48-bit address
    ///
    /// Can pack 16 + [`align_of::<T>()`] bits of data into a pointer.
    pub struct Level4Paging(true, 16);
}

#[cfg(target_arch = "aarch64")]
ptr_cfg! {
    /// 52-bit address
    ///
    /// Can pack 12 + [`align_of::<T>()`] bits of data into a pointer.
    pub struct Lva(true, 12);
}

#[cfg(target_arch = "aarch64")]
ptr_cfg! {
    /// 48-bit address
    ///
    /// Can pack 16 + [`align_of::<T>()`] bits of data into a pointer.
    pub struct Level4Paging(true, 16);
}

#[cfg(target_arch = "aarch64")]
ptr_cfg! {
    /// 39-bit address
    ///
    /// Can pack 25 + [`align_of::<T>()`] bits of data into a pointer.
    pub struct Level3Paging(true, 25);
}

#[cfg(target_arch = "riscv64")]
ptr_cfg! {
    /// 57-bit address
    ///
    /// Can pack 7 + [`align_of::<T>()`] bits of data into a pointer.
    pub struct Sv57(true, 7);
}

#[cfg(target_arch = "riscv64")]
ptr_cfg! {
    /// 48-bit address
    ///
    /// Can pack 16 + [`align_of::<T>()`] bits of data into a pointer.
    pub struct Sv48(true, 16);
}

#[cfg(target_arch = "riscv64")]
ptr_cfg! {
    /// 39-bit address
    ///
    /// Can pack 25 + [`align_of::<T>()`] bits of data into a pointer.
    pub struct Sv39(true, 25);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn none() {
        assert_eq!(None::lsb_bits::<u32>(), 0);
        assert_eq!(None::msb_bits(), 0);
        assert_eq!(None::bits::<u32>(), 0);
    }

    #[test]
    fn align_only() {
        assert_eq!(AlignOnly::lsb_bits::<u32>(), 2);
        assert_eq!(AlignOnly::lsb_bits::<u64>(), 3);
        assert_eq!(AlignOnly::lsb_bits::<u8>(), 0);
        assert_eq!(AlignOnly::msb_bits(), 0);
        assert_eq!(AlignOnly::bits::<u32>(), 2);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn level5paging() {
        assert_eq!(Level5Paging::lsb_bits::<u32>(), 2);
        assert_eq!(Level5Paging::msb_bits(), 7);
        assert_eq!(Level5Paging::bits::<u32>(), 9);
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn level4paging() {
        assert_eq!(Level4Paging::lsb_bits::<u32>(), 2);
        assert_eq!(Level4Paging::msb_bits(), 16);
        assert_eq!(Level4Paging::bits::<u32>(), 18);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn lva() {
        assert_eq!(Lva::lsb_bits::<u32>(), 2);
        assert_eq!(Lva::msb_bits(), 12);
        assert_eq!(Lva::bits::<u32>(), 14);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn level4paging() {
        assert_eq!(Level4Paging::lsb_bits::<u32>(), 2);
        assert_eq!(Level4Paging::msb_bits(), 16);
        assert_eq!(Level4Paging::bits::<u32>(), 18);
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn level3paging() {
        assert_eq!(Level3Paging::lsb_bits::<u32>(), 2);
        assert_eq!(Level3Paging::msb_bits(), 25);
        assert_eq!(Level3Paging::bits::<u32>(), 27);
    }

    #[cfg(target_arch = "riscv64")]
    #[test]
    fn sv57() {
        assert_eq!(Sv57::lsb_bits::<u32>(), 2);
        assert_eq!(Sv57::msb_bits(), 7);
        assert_eq!(Sv57::bits::<u32>(), 9);
    }

    #[cfg(target_arch = "riscv64")]
    #[test]
    fn sv48() {
        assert_eq!(Sv48::lsb_bits::<u32>(), 2);
        assert_eq!(Sv48::msb_bits(), 16);
        assert_eq!(Sv48::bits::<u32>(), 18);
    }

    #[cfg(target_arch = "riscv64")]
    #[test]
    fn sv39() {
        assert_eq!(Sv39::lsb_bits::<u32>(), 2);
        assert_eq!(Sv39::msb_bits(), 25);
        assert_eq!(Sv39::bits::<u32>(), 27);
    }
}
