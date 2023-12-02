use core::mem::{align_of, size_of};

use sptr::Strict;

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
/// This configuration will always fail when packing data into a pointer.
/// * [`AlignOnly`]: Only the alignment of the pointer can be packed into the pointer.
/// This configuration will use the alignment of a pointer to determine how many bits can be packed
/// into the LSBs of the pointer.
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

pub(crate) trait PtrCfgExt: PtrCfg {
    fn lsb_bits_mask<T>() -> usize {
        (1 << Self::lsb_bits::<T>()) - 1
    }

    #[allow(clippy::cast_possible_truncation)]
    fn msb_bits_mask() -> usize {
        const PTR_SIZE: usize = size_of::<*const ()>() * 8;
        (!0usize)
            .checked_shl((PTR_SIZE - Self::msb_bits()) as u32)
            .unwrap_or(0)
    }

    /// Checks if pointer would be modified by [`PackedPtr::new`](crate::PackedPtr::new).
    /// If this returns false, it would be unsafe to create a `PackedPtr` with this
    /// pointer & config.
    fn check_ptr<T>(ptr: *const T) -> bool {
        let mask = Self::msb_bits_mask() | Self::lsb_bits_mask::<T>();
        Strict::addr(ptr) & mask == 0
    }
}

impl<T: PtrCfg> PtrCfgExt for T {}

macro_rules! ptr_cfg {
    (
        $(#[$outer:meta])*
        $(pub)* struct $cfg:ident($align:literal, $msb:literal);
    ) => {
        $(#[$outer])*
        pub struct $cfg;
        impl private::Sealed for $cfg {}
        impl PtrCfg for $cfg {
            #[must_use]
            fn lsb_bits<T>() -> usize {
                if $align {
                    align_of::<T>().trailing_zeros() as usize
                } else {
                    0
                }
            }
            #[must_use]
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
        assert_eq!(None::lsb_bits_mask::<u32>(), 0x00);
        assert_eq!(None::msb_bits_mask(), 0x00);
        assert!(None::check_ptr::<u32>(sptr::invalid(0xffff_ffff)));
    }

    #[test]
    fn align_only() {
        assert_eq!(AlignOnly::lsb_bits::<u32>(), 2);
        assert_eq!(AlignOnly::lsb_bits::<u64>(), 3);
        assert_eq!(AlignOnly::lsb_bits::<u8>(), 0);
        assert_eq!(AlignOnly::msb_bits(), 0);
        assert_eq!(AlignOnly::bits::<u32>(), 2);
        assert_eq!(AlignOnly::lsb_bits_mask::<u32>(), 0x03);
        assert_eq!(AlignOnly::lsb_bits_mask::<u64>(), 0x07);
        assert_eq!(AlignOnly::lsb_bits_mask::<u8>(), 0x00);
        assert_eq!(AlignOnly::msb_bits_mask(), 0x00);
        assert!(AlignOnly::check_ptr::<u32>(sptr::invalid(0xffff_fffc)));
        assert!(!AlignOnly::check_ptr::<u32>(sptr::invalid(0xffff_ffff)));
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn level5paging() {
        assert_eq!(Level5Paging::lsb_bits::<u32>(), 2);
        assert_eq!(Level5Paging::msb_bits(), 7);
        assert_eq!(Level5Paging::bits::<u32>(), 9);
        assert_eq!(Level5Paging::lsb_bits_mask::<u32>(), 0x03);
        assert_eq!(Level5Paging::msb_bits_mask(), 0xfe00_0000_0000_0000);
        assert!(Level5Paging::check_ptr::<u32>(sptr::invalid(
            0x01ff_ffff_ffff_fffc
        )));
        assert!(!Level5Paging::check_ptr::<u32>(sptr::invalid(
            0xffff_ffff_ffff_ffff
        )));
    }

    #[cfg(target_arch = "x86_64")]
    #[test]
    fn level4paging() {
        assert_eq!(Level4Paging::lsb_bits::<u32>(), 2);
        assert_eq!(Level4Paging::msb_bits(), 16);
        assert_eq!(Level4Paging::bits::<u32>(), 18);
        assert_eq!(Level4Paging::lsb_bits_mask::<u32>(), 0x03);
        assert_eq!(Level4Paging::msb_bits_mask(), 0xffff_0000_0000_0000);
        assert!(Level4Paging::check_ptr::<u32>(sptr::invalid(
            0x0000_ffff_ffff_fffc
        )));
        assert!(!Level4Paging::check_ptr::<u32>(sptr::invalid(
            0xffff_ffff_ffff_ffff
        )));
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn lva() {
        assert_eq!(Lva::lsb_bits::<u32>(), 2);
        assert_eq!(Lva::msb_bits(), 12);
        assert_eq!(Lva::bits::<u32>(), 14);
        assert_eq!(Lva::lsb_bits_mask::<u32>(), 0x03);
        assert_eq!(Lva::msb_bits_mask(), 0xfff0_0000_0000_0000);
        assert!(Lva::check_ptr::<u32>(sptr::invalid(0x000f_ffff_ffff_fffc)));
        assert!(!Lva::check_ptr::<u32>(sptr::invalid(0xffff_ffff_ffff_ffff)));
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn level4paging() {
        assert_eq!(Level4Paging::lsb_bits::<u32>(), 2);
        assert_eq!(Level4Paging::msb_bits(), 16);
        assert_eq!(Level4Paging::bits::<u32>(), 18);
        assert_eq!(Level4Paging::lsb_bits_mask::<u32>(), 0x03);
        assert_eq!(Level4Paging::msb_bits_mask(), 0xffff_0000_0000_0000);
        assert!(Level4Paging::check_ptr::<u32>(sptr::invalid(
            0x0000_ffff_ffff_fffc
        )));
        assert!(!Level4Paging::check_ptr::<u32>(sptr::invalid(
            0xffff_ffff_ffff_ffff
        )));
    }

    #[cfg(target_arch = "aarch64")]
    #[test]
    fn level3paging() {
        assert_eq!(Level3Paging::lsb_bits::<u32>(), 2);
        assert_eq!(Level3Paging::msb_bits(), 25);
        assert_eq!(Level3Paging::bits::<u32>(), 27);
        assert_eq!(Level3Paging::lsb_bits_mask::<u32>(), 0x03);
        assert_eq!(Level3Paging::msb_bits_mask(), 0xffff_ff80_0000_0000);
        assert!(Level3Paging::check_ptr::<u32>(sptr::invalid(
            0x0000_007f_ffff_fffc
        )));
        assert!(!Level3Paging::check_ptr::<u32>(sptr::invalid(
            0xffff_ffff_ffff_ffff
        )));
    }

    #[cfg(target_arch = "riscv64")]
    #[test]
    fn sv57() {
        assert_eq!(Sv57::lsb_bits::<u32>(), 2);
        assert_eq!(Sv57::msb_bits(), 7);
        assert_eq!(Sv57::bits::<u32>(), 9);
        assert_eq!(Sv57::lsb_bits_mask::<u32>(), 0x03);
        assert_eq!(Sv57::msb_bits_mask(), 0xfe00_0000_0000_0000);
        assert!(Sv57::check_ptr::<u32>(sptr::invalid(0x01ff_ffff_ffff_fffc)));
        assert!(!Sv57::check_ptr::<u32>(sptr::invalid(
            0xffff_ffff_ffff_ffff
        )));
    }

    #[cfg(target_arch = "riscv64")]
    #[test]
    fn sv48() {
        assert_eq!(Sv48::lsb_bits::<u32>(), 2);
        assert_eq!(Sv48::msb_bits(), 16);
        assert_eq!(Sv48::bits::<u32>(), 18);
        assert_eq!(Sv48::lsb_bits_mask::<u32>(), 0x03);
        assert_eq!(Sv48::msb_bits_mask(), 0xffff_0000_0000_0000);
        assert!(Sv48::check_ptr::<u32>(sptr::invalid(0x0000_ffff_ffff_fffc)));
        assert!(!Sv48::check_ptr::<u32>(sptr::invalid(
            0xffff_ffff_ffff_ffff
        )));
    }

    #[cfg(target_arch = "riscv64")]
    #[test]
    fn sv39() {
        assert_eq!(Sv39::lsb_bits::<u32>(), 2);
        assert_eq!(Sv39::msb_bits(), 25);
        assert_eq!(Sv39::bits::<u32>(), 27);
        assert_eq!(Sv39::lsb_bits_mask::<u32>(), 0x03);
        assert_eq!(Sv39::msb_bits_mask(), 0xffff_ff80_0000_0000);
        assert!(Sv39::check_ptr::<u32>(sptr::invalid(0x0000_007f_ffff_fffc)));
        assert!(!Sv39::check_ptr::<u32>(sptr::invalid(
            0xffff_ffff_ffff_ffff
        )));
    }
}
