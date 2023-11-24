use sptr::Strict;

use crate::PackedPtrError;

/// The size of a pointer in bytes.
const PTR_SIZE: usize = core::mem::size_of::<usize>();
/// The size of a pointer in bits.
const PTR_SIZE_BITS: usize = PTR_SIZE * 8;

#[cfg(not(feature = "std"))]
static MSB_BITS: spin::Once<usize> = spin::Once::new();
#[cfg(feature = "std")]
static MSB_BITS: std::sync::OnceLock<usize> = std::sync::OnceLock::new();

#[repr(transparent)]
pub struct PackedPtr<T>(*const T);

impl<T> PackedPtr<T> {
    /// Types must be aligned to a specific number of bytes. This gives us some lsb to play with.
    const ALIGNMENT: usize = core::mem::align_of::<T>();
    const ALIGN_BITS: usize = Self::ALIGNMENT.trailing_zeros() as usize;
    const ALIGN_MASK: usize = Self::ALIGNMENT - 1;

    pub fn bits() -> usize {
        Self::msb_bits() + Self::ALIGN_BITS
    }

    #[inline]
    fn msb_bits() -> usize {
        get_msb_bits()
    }

    #[inline]
    fn msb_bits_mask() -> usize {
        !0 << (PTR_SIZE_BITS - Self::msb_bits())
    }
}

impl<T> PackedPtr<T> {
    pub fn new(ptr: *const T, data: usize) -> Result<Self, PackedPtrError> {
        if Strict::addr(ptr) & Self::ALIGN_MASK != 0 {
            return Err(PackedPtrError::UnalignedAddress);
        }

        if data >= 1 << Self::bits() {
            return Err(PackedPtrError::DataOverflow);
        }

        // SAFETY: We have already checked that the pointer is aligned and that the data will fit in
        // the pointer.
        Ok(unsafe { Self::new_unchecked(ptr, data) })
    }

    pub unsafe fn new_unchecked(ptr: *const T, data: usize) -> Self {
        let bits = Self::bits();
        let trunc_data = data & ((1 << bits) - 1);
        let upper = (trunc_data << (PTR_SIZE_BITS - bits)) & Self::msb_bits_mask();
        let lower = trunc_data & Self::ALIGN_MASK;

        let ptr = Strict::map_addr(ptr, |addr| addr | upper | lower);
        Self(ptr)
    }

    pub fn get(self) -> (*const T, usize) {
        let ptr = self.ptr();
        let data = self.data();
        (ptr, data)
    }

    pub fn ptr(self) -> *const T {
        Strict::map_addr(self.0, |addr| {
            addr & !Self::msb_bits_mask() & !Self::ALIGN_MASK
        })
    }

    pub fn data(self) -> usize {
        let addr = Strict::addr(self.0);
        let upper = addr & Self::msb_bits_mask();
        let lower = addr & Self::ALIGN_MASK;
        (upper >> (PTR_SIZE_BITS - Self::bits())) | lower
    }
}

super::impl_ptr!(PackedPtr);

#[cfg(not(feature = "std"))]
fn get_msb_bits() -> usize {
    *MSB_BITS.call_once(|| {
        if check_5th_lvl_paging() {
            PTR_SIZE_BITS - 57
        } else {
            PTR_SIZE_BITS - 48
        }
    })
}

#[cfg(feature = "std")]
fn get_msb_bits() -> usize {
    *MSB_BITS.get_or_init(|| {
        if check_5th_lvl_paging() {
            PTR_SIZE_BITS - 57
        } else {
            PTR_SIZE_BITS - 48
        }
    })
}

#[cfg(all(feature = "libc", unix))]
/// Checks if 5-level paging is supported by the kernel.
/// This is done by trying to map a page at a 48-bit address.
///
/// See <https://docs.kernel.org/next/x86/x86_64/5level-paging.html>
fn check_5th_lvl_paging() -> bool {
    const HIGH_ADDR: usize = 1 << 48;
    const PAGE_SIZE: usize = 4 << 10;

    let ret = unsafe {
        libc::mmap(
            sptr::invalid_mut(HIGH_ADDR),
            2 * PAGE_SIZE,
            libc::PROT_READ | libc::PROT_WRITE,
            libc::MAP_PRIVATE | libc::MAP_ANONYMOUS,
            -1,
            0,
        )
    };

    if ret == libc::MAP_FAILED {
        false
    } else {
        // Per https://github.com/rust-lang/miri/issues/3041, munmap throws a warning when called.
        // There is no way to suppress this warning, so this comment will have to do.
        unsafe { libc::munmap(ret, 2 * PAGE_SIZE) };

        // Check if ret in the 57-bit address space.
        Strict::addr(ret) >= HIGH_ADDR
    }
}

#[cfg(all(feature = "libc", windows))]
/// Supposedly Windows supports 5-level paging.
/// However, I have not been able to find any documentation on how to check for it or even if it is
/// supported. The only evidence I have found is this tweet: <https://twitter.com/aionescu/status/1142637363840946176>
///
/// According to <https://learn.microsoft.com/en-us/windows/win32/memory/memory-limits-for-windows-releases>
/// 64-bit Windows supports 128 TiB of virtual memory, which means 48-bit addressing & 4-level
/// paging.
const fn check_5th_lvl_paging() -> bool {
    false
}

#[cfg(all(feature = "libc", not(unix), not(windows)))]
/// Fallback implementation for when the target is not unix.
/// Assumes that 5-level paging is supported.
const fn check_5th_lvl_paging() -> bool {
    true
}

#[cfg(not(feature = "libc"))]
/// Fallback implementation for when libc is not available.
/// Assumes that 5-level paging is supported.
/// This is not a good assumption, but it is the safest one.
const fn check_5th_lvl_paging() -> bool {
    true
}
