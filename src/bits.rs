//! Bit-level packing of data into the unused bits of an address.
//!
//! Data is stored in the upper `msb_bits` and lower `lsb_bits` bits of a `usize`. The lower
//! `lsb_bits` bits of the data go into the lower bits of the address, and the next `msb_bits` bits
//! of the data go into the upper bits of the address.
//!
//! The functions in this module are formally verified in `proofs/`. In particular, if [`check`]
//! returns `Ok(())`, then [`pack_addr`] followed by [`unpack_addr`] and [`unpack_data`] never
//! panics and returns the original address and data (`bits.pack_unpack_roundtrip`).

use crate::PackedPtrError;

/// Returns a mask with the lower `lsb_bits` bits set.
///
/// The result is `2^min(lsb_bits, BITS) - 1`, so any `lsb_bits >= usize::BITS` gives `usize::MAX`.
/// Never panics.
#[inline]
pub const fn lsb_bits_mask(lsb_bits: usize) -> usize {
    if lsb_bits >= usize::BITS as usize {
        usize::MAX
    } else {
        (1usize << lsb_bits) - 1
    }
}

/// Returns a mask with the upper `msb_bits` bits set.
///
/// The result is `2^BITS - 2^(BITS - min(msb_bits, BITS))`, so any `msb_bits >= usize::BITS` gives
/// `usize::MAX`. Never panics.
///
/// If `msb_bits + lsb_bits <= usize::BITS`, this mask is disjoint with
/// [`lsb_bits_mask(lsb_bits)`](lsb_bits_mask).
#[inline]
pub const fn msb_bits_mask(msb_bits: usize) -> usize {
    if msb_bits == 0 {
        0
    } else {
        usize::MAX << ((usize::BITS as usize).saturating_sub(msb_bits))
    }
}

/// Packs `data` into the upper `msb_bits` and lower `lsb_bits` bits of `addr`.
///
/// The lower `lsb_bits` bits of `data` are stored in the lower bits of the result, and the next
/// `msb_bits` bits of `data` are stored in the upper bits. Any higher bits of `data` are discarded.
///
/// # Preconditions
///
/// - `msb_bits + lsb_bits <= usize::BITS`
/// - `addr` is zero in its upper `msb_bits` bits and its lower `lsb_bits` bits
///
/// Both hold whenever [`check`] returns `Ok(())`. Under these preconditions, the function never
/// panics, [`unpack_addr`] of the result returns `addr`, and, if `data < 2^(msb_bits + lsb_bits)`,
/// [`unpack_data`] of the result returns `data`.
///
/// If a precondition is violated, the result & behavior are unspecified.
#[inline]
pub const fn pack_addr(addr: usize, data: usize, msb_bits: usize, lsb_bits: usize) -> usize {
    debug_assert!(msb_bits + lsb_bits <= usize::BITS as usize);

    let upper = if msb_bits == 0 {
        0
    } else {
        (data >> lsb_bits) << (usize::BITS as usize - msb_bits)
    };
    let lower = data & lsb_bits_mask(lsb_bits);

    addr | upper | lower
}

/// Extracts the address from a packed value by clearing its upper `msb_bits` and lower `lsb_bits`
/// bits.
///
/// Never panics. If `packed` was produced by [`pack_addr`] with the same `msb_bits` and `lsb_bits`
/// and its preconditions held, the result is the original address.
#[inline]
pub const fn unpack_addr(packed: usize, msb_bits: usize, lsb_bits: usize) -> usize {
    packed & !msb_bits_mask(msb_bits) & !lsb_bits_mask(lsb_bits)
}

/// Extracts the data from a packed value.
///
/// The lower `lsb_bits` bits of `packed` become the lower bits of the result, and the upper
/// `msb_bits` bits of `packed` are placed directly above them.
///
/// # Preconditions
///
/// - `msb_bits + lsb_bits <= usize::BITS`
///
/// Under this precondition the function never panics. If `packed` was produced by [`pack_addr`]
/// with the same `msb_bits` and `lsb_bits`, its preconditions held, and the data satisfied
/// `data < 2^(msb_bits + lsb_bits)`, the result is the original data.
///
/// If the precondition is violated, the result & behavior are unspecified.
#[inline]
pub const fn unpack_data(packed: usize, msb_bits: usize, lsb_bits: usize) -> usize {
    debug_assert!(msb_bits + lsb_bits <= usize::BITS as usize);

    let lower = packed & lsb_bits_mask(lsb_bits);

    if msb_bits == 0 {
        lower
    } else {
        let upper = packed & msb_bits_mask(msb_bits);
        lower | (upper >> (usize::BITS as usize - msb_bits - lsb_bits))
    }
}

/// Returns `true` iff the configuration is invalid or `addr` uses its upper `msb_bits` bits.
///
/// That is, iff `msb_bits + lsb_bits > usize::BITS` or `addr >= 2^(BITS - msb_bits)`. Never panics,
/// even if `msb_bits + lsb_bits` overflows.
#[inline]
const fn is_unsafe_config(addr: usize, msb_bits: usize, lsb_bits: usize) -> bool {
    msb_bits.saturating_add(lsb_bits) > usize::BITS as usize || addr & msb_bits_mask(msb_bits) != 0
}

/// Returns `true` iff `addr` is not aligned to `2^lsb_bits`, i.e. any of its lower `lsb_bits` bits
/// are set.
///
/// Never panics.
#[inline]
const fn is_unaligned_addr(addr: usize, lsb_bits: usize) -> bool {
    addr & lsb_bits_mask(lsb_bits) != 0
}

/// Returns `true` iff `data` does not fit in `msb_bits + lsb_bits` bits, i.e.
/// `data >= 2^(msb_bits + lsb_bits)`.
///
/// Never panics.
#[inline]
const fn is_unsafe_data(data: usize, msb_bits: usize, lsb_bits: usize) -> bool {
    ((usize::BITS - data.leading_zeros()) as usize) > msb_bits.saturating_add(lsb_bits)
}

/// Checks that `data` can be packed into `addr` and recovered without loss.
///
/// Never panics. Returns `Ok(())` iff all of the following hold:
///
/// - `msb_bits + lsb_bits <= usize::BITS`
/// - `addr` is zero in its upper `msb_bits` bits
/// - `addr` is zero in its lower `lsb_bits` bits
/// - `data < 2^(msb_bits + lsb_bits)`
///
/// In that case [`pack_addr`], [`unpack_addr`] and [`unpack_data`] never panic, and unpacking the
/// packed value returns the original `addr` and `data`.
///
/// # Errors
///
/// - [`PackedPtrError::UnsafeConfig`] if `msb_bits + lsb_bits > usize::BITS` or `addr` has any of
///   its upper `msb_bits` bits set.
/// - [`PackedPtrError::UnalignedAddress`] if `addr` has any of its lower `lsb_bits` bits set.
/// - [`PackedPtrError::DataOverflow`] if `data` does not fit in `msb_bits + lsb_bits` bits.
#[inline]
pub const fn check(
    addr: usize,
    data: usize,
    msb_bits: usize,
    lsb_bits: usize,
) -> Result<(), PackedPtrError> {
    if is_unsafe_config(addr, msb_bits, lsb_bits) {
        return Err(PackedPtrError::UnsafeConfig);
    }

    if is_unaligned_addr(addr, lsb_bits) {
        return Err(PackedPtrError::UnalignedAddress);
    }

    if is_unsafe_data(data, msb_bits, lsb_bits) {
        return Err(PackedPtrError::DataOverflow);
    }

    Ok(())
}

/// Tests derived from the mathematical definitions in `proofs/PackedPtr/Defs.lean` and the
/// theorems in `proofs/PackedPtr/Proofs.lean`.
#[cfg(test)]
mod tests {
    use super::*;

    const BITS: usize = usize::BITS as usize;

    const SMALL_BIT_COUNTS: [usize; 12] = [
        0,
        1,
        2,
        3,
        7,
        8,
        BITS / 2,
        BITS - 8,
        BITS - 3,
        BITS - 2,
        BITS - 1,
        BITS,
    ];

    const HUGE_BIT_COUNTS: [usize; 6] = [
        BITS + 1,
        2 * BITS,
        usize::MAX / 2,
        usize::MAX / 2 + 1,
        usize::MAX - 1,
        usize::MAX,
    ];

    /// Transcription of `proofs/PackedPtr/Defs.lean`.
    mod spec {
        use super::BITS;

        /// `2 ^ e`
        pub fn pow2(e: usize) -> u128 {
            assert!(e < 128, "2^{e} is not representable");
            1 << e
        }

        /// `x < 2 ^ e` for an arbitrarily large exponent.
        fn lt_pow2(x: u128, e: u128) -> bool {
            e >= 128 || x < 1 << e
        }

        /// `m + n ≤ Usize.numBits`
        pub fn valid_config(m: usize, n: usize) -> bool {
            m as u128 + n as u128 <= BITS as u128
        }

        /// `addr < 2 ^ (Usize.numBits - m)`
        pub fn addr_fits(addr: u128, m: usize) -> bool {
            addr < pow2(BITS.saturating_sub(m))
        }

        /// `addr % 2 ^ n = 0`
        pub fn addr_aligned(addr: u128, n: usize) -> bool {
            if n >= 128 {
                addr == 0
            } else {
                addr % pow2(n) == 0
            }
        }

        /// `addr_aligned addr n and addr_fits addr m`
        pub fn clean_addr(addr: u128, m: usize, n: usize) -> bool {
            addr_aligned(addr, n) && addr_fits(addr, m)
        }

        /// `data < 2 ^ (m + n)`
        pub fn data_fits(data: u128, m: usize, n: usize) -> bool {
            lt_pow2(data, m as u128 + n as u128)
        }

        /// `addr + data % 2 ^ n + data / 2 ^ n % 2 ^ m * 2 ^ (Usize.numBits - m)`
        pub fn pack(addr: u128, data: u128, m: usize, n: usize) -> u128 {
            addr + data % pow2(n) + data / pow2(n) % pow2(m) * pow2(BITS.saturating_sub(m))
        }

        /// `packed % 2 ^ (Usize.numBits - m) / 2 ^ n * 2 ^ n`
        pub fn unpack_addr(packed: u128, m: usize, n: usize) -> u128 {
            packed % pow2(BITS.saturating_sub(m)) / pow2(n) * pow2(n)
        }

        /// `packed % 2 ^ n + packed / 2 ^ (Usize.numBits - m) * 2 ^ n`
        pub fn unpack_data(packed: u128, m: usize, n: usize) -> u128 {
            packed % pow2(n) + packed / pow2(BITS.saturating_sub(m)) * pow2(n)
        }
    }

    fn to_usize(x: u128) -> usize {
        usize::try_from(x).expect("spec value does not fit in a usize")
    }

    fn bit_counts() -> impl Iterator<Item = usize> + Clone {
        SMALL_BIT_COUNTS.into_iter().chain(HUGE_BIT_COUNTS)
    }

    fn configs() -> impl Iterator<Item = (usize, usize)> + Clone {
        bit_counts().flat_map(|m| bit_counts().map(move |n| (m, n)))
    }

    /// Every `(m, n)` pair satisfying `valid_config`.
    fn valid_configs() -> impl Iterator<Item = (usize, usize)> + Clone {
        configs().filter(|&(m, n)| spec::valid_config(m, n))
    }

    /// Boundary values: `2^i - 1`, `2^i` and `2^i + 1` for every bit `i`, plus a few bit patterns.
    ///
    /// Every threshold in the spec is a power of two, so this lands on both sides of each one.
    fn values() -> impl Iterator<Item = usize> + Clone {
        let around_powers = (0..BITS).flat_map(|i| {
            let p = 1usize << i;
            [p - 1, p, p.wrapping_add(1)]
        });
        #[allow(clippy::cast_possible_truncation)]
        let patterns = [
            usize::MAX,
            usize::MAX - 1,
            usize::MAX / 3,          // 0b0101...
            usize::MAX / 3 * 2,      // 0b1010...
            usize::MAX / 5,          // 0b0011...
            usize::MAX / 17,         // 0b00001111...
            usize::MAX / 255 * 0x80, // top bit of every byte
            0x9E37_79B9_7F4A_7C15_u64 as usize,
            0xDEAD_BEEF_CAFE_F00D_u64 as usize,
        ];
        around_powers.chain(patterns)
    }

    /// Turns an arbitrary value into one satisfying `clean_addr` by zeroing its upper `m` and lower
    /// `n` bits. Requires `valid_config m n`.
    fn clean(v: usize, m: usize, n: usize) -> usize {
        let addr = spec::unpack_addr(v as u128, m, n);
        assert!(spec::clean_addr(addr, m, n));
        to_usize(addr)
    }

    /// Truncates a value so that it satisfies `data_fits`. Requires `valid_config m n`.
    fn fit(v: usize, m: usize, n: usize) -> usize {
        let data = v as u128 % spec::pow2(m + n);
        assert!(spec::data_fits(data, m, n));
        to_usize(data)
    }

    /// Sanity checks the grid
    #[test]
    fn grid_covers_edges() {
        assert!(valid_configs().any(|c| c == (0, 0)));
        assert!(valid_configs().any(|c| c == (0, BITS)));
        assert!(valid_configs().any(|c| c == (BITS, 0)));
        assert!(valid_configs().any(|(m, n)| m > 0 && n > 0 && m + n == BITS));
        assert!(valid_configs().any(|(m, n)| m > 0 && n > 0 && m + n < BITS));
        assert!(configs().any(|(m, n)| m.checked_add(n).is_none()));
        assert!(configs().any(|(m, n)| m <= BITS && n <= BITS && m + n == BITS + 1));

        assert!(values().any(|v| v == 0));
        assert!(values().any(|v| v == usize::MAX));
        assert!(values().any(|v| v == 1 << (BITS - 1)));
    }

    // ---------------------------------------------------------------------------------------------
    // bits.lsb_bits_mask_spec: r = 2 ^ min(n, BITS) - 1
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn lsb_bits_mask_examples() {
        assert_eq!(lsb_bits_mask(0), 0);
        assert_eq!(lsb_bits_mask(1), 1);
        assert_eq!(lsb_bits_mask(3), 7);
        assert_eq!(lsb_bits_mask(8), 255);
        assert_eq!(lsb_bits_mask(BITS - 1), usize::MAX / 2);
        assert_eq!(lsb_bits_mask(BITS), usize::MAX);
    }

    #[test]
    fn lsb_bits_mask_saturates() {
        for n in HUGE_BIT_COUNTS {
            assert_eq!(lsb_bits_mask(n), usize::MAX, "n = {n}");
        }
    }

    #[test]
    fn lsb_bits_mask_matches_spec() {
        for n in (0..=BITS + 1).chain(HUGE_BIT_COUNTS) {
            let expected = spec::pow2(n.min(BITS)) - 1;
            assert_eq!(lsb_bits_mask(n) as u128, expected, "n = {n}");
        }
    }

    // ---------------------------------------------------------------------------------------------
    // bits.msb_bits_mask_spec: r = 2 ^ BITS - 2 ^ (BITS - min(m, BITS))
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn msb_bits_mask_examples() {
        assert_eq!(msb_bits_mask(0), 0);
        assert_eq!(msb_bits_mask(1), usize::MAX - usize::MAX / 2);
        assert_eq!(msb_bits_mask(8), usize::MAX - usize::MAX / 256);
        assert_eq!(msb_bits_mask(BITS - 1), usize::MAX - 1);
        assert_eq!(msb_bits_mask(BITS), usize::MAX);
    }

    #[test]
    fn msb_bits_mask_saturates() {
        for m in HUGE_BIT_COUNTS {
            assert_eq!(msb_bits_mask(m), usize::MAX, "m = {m}");
        }
    }

    #[test]
    fn msb_bits_mask_matches_spec() {
        for m in (0..=BITS + 1).chain(HUGE_BIT_COUNTS) {
            let expected = spec::pow2(BITS) - spec::pow2(BITS - m.min(BITS));
            assert_eq!(msb_bits_mask(m) as u128, expected, "m = {m}");
        }
    }

    // ---------------------------------------------------------------------------------------------
    // bits.bits_mask_disjoint: valid_config m n -> lsb_bits_mask n &&& msb_bits_mask m = 0
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn masks_are_disjoint_for_every_valid_config() {
        for m in 0..=BITS {
            for n in 0..=BITS - m {
                assert!(spec::valid_config(m, n));
                assert_eq!(lsb_bits_mask(n) & msb_bits_mask(m), 0, "m = {m}, n = {n}");
            }
        }
    }

    /// When `m + n = BITS` the two masks are disjoint and together cover every bit.
    #[test]
    fn masks_partition_the_word_when_config_is_full() {
        for m in 0..=BITS {
            let n = BITS - m;
            assert_eq!(lsb_bits_mask(n) ^ msb_bits_mask(m), usize::MAX, "m = {m}");
        }
    }

    // ---------------------------------------------------------------------------------------------
    // bits.pack_addr_spec: valid_config m n -> clean_addr a m n -> r = pack a d m n
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn pack_addr_examples() {
        // No data bits at all: the address is returned untouched, whatever the data.
        assert_eq!(pack_addr(0x1234, 0, 0, 0), 0x1234);
        assert_eq!(pack_addr(0x1234, usize::MAX, 0, 0), 0x1234);

        // Only low bits: 0x1000 + 0b101
        assert_eq!(pack_addr(0x1000, 0b101, 0, 3), 0x1005);

        // Only high bits: 0x1000 + 0xAB * 2^(BITS - 8)
        assert_eq!(pack_addr(0x1000, 0xAB, 8, 0), 0x1000 + (0xAB << (BITS - 8)));

        // Both: data = 0b10110_101 splits into low 0b101 and high 0b10110.
        assert_eq!(
            pack_addr(0x1000, 0b1011_0101, 8, 3),
            0x1000 + 0b101 + (0b10110 << (BITS - 8))
        );

        // Maximal data fills exactly the m + n data bits.
        assert_eq!(
            pack_addr(0x1000, (1 << 11) - 1, 8, 3),
            0x1000 + 7 + (0xFF << (BITS - 8))
        );
    }

    /// With `m + n = BITS` the only clean address is zero and the data occupies the whole word.
    #[test]
    fn pack_addr_full_config_examples() {
        // All bits low: packed = data
        assert_eq!(pack_addr(0, usize::MAX, 0, BITS), usize::MAX);
        assert_eq!(pack_addr(0, 0x1234, 0, BITS), 0x1234);

        // All bits high: packed = data
        assert_eq!(pack_addr(0, usize::MAX, BITS, 0), usize::MAX);
        assert_eq!(pack_addr(0, 0x1234, BITS, 0), 0x1234);

        // Split 8 / BITS - 8: the low BITS - 8 bits stay put, the next 8 land on top of them.
        assert_eq!(pack_addr(0, usize::MAX, 8, BITS - 8), usize::MAX);
        assert_eq!(pack_addr(0, 0x1234, 8, BITS - 8), 0x1234);
    }

    /// Bits of `data` above `m + n` are discarded: `data / 2^n % 2^m` drops them.
    #[test]
    fn pack_addr_discards_excess_data() {
        let expected = 0x1000 + 0b101 + (0b10110 << (BITS - 8));
        assert_eq!(pack_addr(0x1000, 0b1011_0101 | 1 << 11, 8, 3), expected);
        assert_eq!(pack_addr(0x1000, 0b1011_0101 | !0 << 11, 8, 3), expected);
    }

    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn pack_addr_matches_spec() {
        for (m, n) in valid_configs() {
            for addr in values().map(|v| clean(v, m, n)) {
                // The theorem does not require `data_fits`
                for data in values() {
                    let expected = spec::pack(addr as u128, data as u128, m, n);
                    assert_eq!(
                        pack_addr(addr, data, m, n) as u128,
                        expected,
                        "addr = {addr:#x}, data = {data:#x}, m = {m}, n = {n}"
                    );
                }
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    // bits.unpack_addr_spec: valid_config m n → r = unpack_addr p m n
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn unpack_addr_examples() {
        // Nothing to clear
        assert_eq!(unpack_addr(usize::MAX, 0, 0), usize::MAX);

        // Clear the low 3 bits
        assert_eq!(unpack_addr(0x1005, 0, 3), 0x1000);
        assert_eq!(unpack_addr(usize::MAX, 0, 3), usize::MAX - 7);

        // Clear the high 8 bits
        assert_eq!(unpack_addr(0x1000 + (0xAB << (BITS - 8)), 8, 0), 0x1000);
        assert_eq!(unpack_addr(usize::MAX, 8, 0), usize::MAX >> 8);

        // Clear both
        assert_eq!(unpack_addr(usize::MAX, 8, 3), (usize::MAX >> 8) - 7);

        // Every bit is a data bit
        assert_eq!(unpack_addr(usize::MAX, 0, BITS), 0);
        assert_eq!(unpack_addr(usize::MAX, BITS, 0), 0);
        assert_eq!(unpack_addr(usize::MAX, 8, BITS - 8), 0);
    }

    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn unpack_addr_matches_spec() {
        for (m, n) in valid_configs() {
            for packed in values() {
                let expected = spec::unpack_addr(packed as u128, m, n);
                assert_eq!(
                    unpack_addr(packed, m, n) as u128,
                    expected,
                    "packed = {packed:#x}, m = {m}, n = {n}"
                );
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    // bits.unpack_data_spec: valid_config m n → r = unpack_data p m n
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn unpack_data_examples() {
        // No data bits
        assert_eq!(unpack_data(usize::MAX, 0, 0), 0);

        // Only low bits
        assert_eq!(unpack_data(0x1005, 0, 3), 0b101);

        // Only high bits
        assert_eq!(unpack_data(0x1000 + (0xAB << (BITS - 8)), 8, 0), 0xAB);

        // Both: high 0b10110 is placed directly above low 0b101
        assert_eq!(
            unpack_data(0x1000 + 0b101 + (0b10110 << (BITS - 8)), 8, 3),
            0b1011_0101
        );
        assert_eq!(unpack_data(usize::MAX, 8, 3), (1 << 11) - 1);

        // Every bit is a data bit
        assert_eq!(unpack_data(usize::MAX, 0, BITS), usize::MAX);
        assert_eq!(unpack_data(usize::MAX, BITS, 0), usize::MAX);
        assert_eq!(unpack_data(0x1234, 8, BITS - 8), 0x1234);
    }

    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn unpack_data_matches_spec() {
        for (m, n) in valid_configs() {
            for packed in values() {
                let expected = spec::unpack_data(packed as u128, m, n);
                assert_eq!(
                    unpack_data(packed, m, n) as u128,
                    expected,
                    "packed = {packed:#x}, m = {m}, n = {n}"
                );
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    // unpack_addr_pack: valid_config m n → clean_addr a m n → unpack_addr (pack a d m n) m n = a
    // ---------------------------------------------------------------------------------------------

    /// The address survives even when the data does not fit.
    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn unpack_addr_inverts_pack_addr() {
        for (m, n) in valid_configs() {
            for addr in values().map(|v| clean(v, m, n)) {
                for data in values() {
                    let packed = pack_addr(addr, data, m, n);
                    assert_eq!(
                        unpack_addr(packed, m, n),
                        addr,
                        "addr = {addr:#x}, data = {data:#x}, m = {m}, n = {n}"
                    );
                }
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    // unpack_data_pack: valid_config m n → clean_addr a m n → data_fits d m n
    //   → unpack_data (pack a d m n) m n = d
    // ---------------------------------------------------------------------------------------------

    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn unpack_data_inverts_pack_addr() {
        for (m, n) in valid_configs() {
            for addr in values().map(|v| clean(v, m, n)) {
                for data in values().map(|v| fit(v, m, n)) {
                    let packed = pack_addr(addr, data, m, n);
                    assert_eq!(
                        unpack_data(packed, m, n),
                        data,
                        "addr = {addr:#x}, data = {data:#x}, m = {m}, n = {n}"
                    );
                }
            }
        }
    }

    /// Without `data_fits`, what comes back is the data truncated to `m + n` bits.
    #[test]
    fn unpack_data_truncates_excess_data() {
        assert_eq!(
            unpack_data(pack_addr(0x1000, usize::MAX, 8, 3), 8, 3),
            (1 << 11) - 1
        );
        assert_eq!(unpack_data(pack_addr(0x1000, 1 << 11, 8, 3), 8, 3), 0);
        assert_eq!(unpack_data(pack_addr(0x1000, usize::MAX, 0, 0), 0, 0), 0);
    }

    // ---------------------------------------------------------------------------------------------
    // bits.is_unsafe_config_spec: r = true ↔ ¬(valid_config m n ∧ addr_fits a m)
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn is_unsafe_config_examples() {
        // Valid config, address below 2^(BITS - m)
        assert!(!is_unsafe_config(0, 0, 0));
        assert!(!is_unsafe_config(usize::MAX, 0, 0));
        assert!(!is_unsafe_config(usize::MAX, 0, BITS));
        assert!(!is_unsafe_config(usize::MAX >> 8, 8, 3));
        assert!(!is_unsafe_config(0, BITS, 0));
        assert!(!is_unsafe_config(0, 8, BITS - 8));

        // Valid config, address at or above 2^(BITS - m)
        assert!(is_unsafe_config((usize::MAX >> 8) + 1, 8, 3));
        assert!(is_unsafe_config(usize::MAX, 1, 0));
        assert!(is_unsafe_config(1, BITS, 0));

        // m + n > BITS
        assert!(is_unsafe_config(0, 1, BITS));
        assert!(is_unsafe_config(0, BITS, 1));
        assert!(is_unsafe_config(0, BITS / 2 + 1, BITS / 2));
        assert!(is_unsafe_config(0, 0, BITS + 1));
        assert!(is_unsafe_config(0, BITS + 1, 0));
    }

    /// `m + n` is a sum of naturals: it must not wrap around to something `<= BITS`.
    #[test]
    fn is_unsafe_config_handles_overflowing_sum() {
        assert!(is_unsafe_config(0, usize::MAX, 1));
        assert!(is_unsafe_config(0, 1, usize::MAX));
        assert!(is_unsafe_config(0, usize::MAX, usize::MAX));
        assert!(is_unsafe_config(0, usize::MAX / 2 + 1, usize::MAX / 2 + 1));
        assert!(is_unsafe_config(0, usize::MAX - BITS + 1, BITS));
    }

    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn is_unsafe_config_matches_spec() {
        for (m, n) in configs() {
            for addr in values() {
                let expected = !(spec::valid_config(m, n) && spec::addr_fits(addr as u128, m));
                assert_eq!(
                    is_unsafe_config(addr, m, n),
                    expected,
                    "addr = {addr:#x}, m = {m}, n = {n}"
                );
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    // bits.is_unaligned_addr_spec: r = true ↔ ¬addr_aligned a n
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn is_unaligned_addr_examples() {
        // Everything is a multiple of 2^0
        assert!(!is_unaligned_addr(0, 0));
        assert!(!is_unaligned_addr(1, 0));
        assert!(!is_unaligned_addr(usize::MAX, 0));

        assert!(!is_unaligned_addr(8, 3));
        assert!(!is_unaligned_addr(0x1000, 12));
        assert!(is_unaligned_addr(4, 3));
        assert!(is_unaligned_addr(9, 3));
        assert!(is_unaligned_addr(0x1000, 13));
        assert!(is_unaligned_addr(usize::MAX, 1));

        // The largest alignment a non-zero usize can have
        assert!(!is_unaligned_addr(1 << (BITS - 1), BITS - 1));
        assert!(is_unaligned_addr(1 << (BITS - 1), BITS));
    }

    /// Zero is a multiple of everything. No other `usize` is a multiple of `2^n` for `n >= BITS`.
    #[test]
    fn is_unaligned_addr_with_huge_alignment() {
        for n in core::iter::once(BITS).chain(HUGE_BIT_COUNTS) {
            assert!(!is_unaligned_addr(0, n), "n = {n}");
            for addr in values().filter(|&v| v != 0) {
                assert!(is_unaligned_addr(addr, n), "addr = {addr:#x}, n = {n}");
            }
        }
    }

    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn is_unaligned_addr_matches_spec() {
        for n in (0..=BITS + 1).chain(HUGE_BIT_COUNTS) {
            for addr in values() {
                let expected = !spec::addr_aligned(addr as u128, n);
                assert_eq!(
                    is_unaligned_addr(addr, n),
                    expected,
                    "addr = {addr:#x}, n = {n}"
                );
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    // bits.is_unsafe_data_spec: r = true ↔ ¬data_fits d m n
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn is_unsafe_data_examples() {
        // 2^0 = 1, so only zero fits in zero bits
        assert!(!is_unsafe_data(0, 0, 0));
        assert!(is_unsafe_data(1, 0, 0));
        assert!(is_unsafe_data(usize::MAX, 0, 0));

        // 11 bits: 2047 fits, 2048 does not, however the bits are split
        for (m, n) in [(8, 3), (3, 8), (11, 0), (0, 11)] {
            assert!(!is_unsafe_data(0, m, n));
            assert!(!is_unsafe_data(2047, m, n));
            assert!(is_unsafe_data(2048, m, n));
            assert!(is_unsafe_data(usize::MAX, m, n));
        }

        // BITS - 1 bits
        assert!(!is_unsafe_data(usize::MAX / 2, BITS - 1, 0));
        assert!(is_unsafe_data(usize::MAX / 2 + 1, BITS - 1, 0));

        // Every usize fits in BITS bits or more
        assert!(!is_unsafe_data(usize::MAX, BITS, 0));
        assert!(!is_unsafe_data(usize::MAX, 0, BITS));
        assert!(!is_unsafe_data(usize::MAX, 8, BITS - 8));
        assert!(!is_unsafe_data(usize::MAX, BITS, BITS));
    }

    /// `m + n` is a sum of naturals: it must not wrap around to something small.
    #[test]
    fn is_unsafe_data_handles_overflowing_sum() {
        assert!(!is_unsafe_data(usize::MAX, usize::MAX, 1));
        assert!(!is_unsafe_data(usize::MAX, 1, usize::MAX));
        assert!(!is_unsafe_data(usize::MAX, usize::MAX, usize::MAX));
        assert!(!is_unsafe_data(1, usize::MAX / 2 + 1, usize::MAX / 2 + 1));
    }

    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn is_unsafe_data_matches_spec() {
        for (m, n) in configs() {
            for data in values() {
                let expected = !spec::data_fits(data as u128, m, n);
                assert_eq!(
                    is_unsafe_data(data, m, n),
                    expected,
                    "data = {data:#x}, m = {m}, n = {n}"
                );
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    // bits.check_spec:
    //   Ok               → valid_config m n && clean_addr a m n && data_fits d m n
    //   UnsafeConfig     → !(valid_config m n && addr_fits a m)
    //   UnalignedAddress → !addr_aligned a n
    //   DataOverflow     → !data_fits d m n
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn check_accepts_examples() {
        assert_eq!(check(0, 0, 0, 0), Ok(()));
        assert_eq!(check(usize::MAX, 0, 0, 0), Ok(()));
        assert_eq!(check(0x1000, 0b1011_0101, 8, 3), Ok(()));
        assert_eq!(check(0x1000, 2047, 8, 3), Ok(()));

        // Largest clean address for m = 8, n = 3
        assert_eq!(check((usize::MAX >> 8) - 7, 2047, 8, 3), Ok(()));

        // Every bit is a data bit
        assert_eq!(check(0, usize::MAX, 0, BITS), Ok(()));
        assert_eq!(check(0, usize::MAX, BITS, 0), Ok(()));
        assert_eq!(check(0, usize::MAX, 8, BITS - 8), Ok(()));
    }

    /// When exactly one condition is violated, the spec leaves only one possible result.
    #[test]
    fn check_rejects_examples() {
        use PackedPtrError::{DataOverflow, UnalignedAddress, UnsafeConfig};

        // m + n > BITS
        assert_eq!(check(0, 0, 1, BITS), Err(UnsafeConfig));
        assert_eq!(check(0, 0, BITS, 1), Err(UnsafeConfig));
        assert_eq!(check(0, 0, usize::MAX, usize::MAX), Err(UnsafeConfig));

        // addr >= 2^(BITS - m)
        assert_eq!(check(1 << (BITS - 8), 0, 8, 3), Err(UnsafeConfig));
        assert_eq!(check(1 << (BITS - 1), 0, 1, 0), Err(UnsafeConfig));

        // addr % 2^n != 0
        assert_eq!(check(0x1004, 0, 8, 3), Err(UnalignedAddress));
        assert_eq!(check(1, 0, 0, 1), Err(UnalignedAddress));
        assert_eq!(check(1 << (BITS - 1), 0, 0, BITS), Err(UnalignedAddress));

        // data >= 2^(m + n)
        assert_eq!(check(0x1000, 2048, 8, 3), Err(DataOverflow));
        assert_eq!(check(0x1000, usize::MAX, 8, 3), Err(DataOverflow));
        assert_eq!(check(0x1000, 1, 0, 0), Err(DataOverflow));
    }

    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn check_matches_spec() {
        let mut accepted = 0usize;
        let mut rejected = [0usize; 3];

        for (m, n) in configs() {
            for addr in values() {
                for data in values() {
                    let (a, d) = (addr as u128, data as u128);
                    // (addr, data, m, n), for failure messages
                    let ctx = (addr, data, m, n);

                    let valid = spec::valid_config(m, n);
                    let all = valid && spec::clean_addr(a, m, n) && spec::data_fits(d, m, n);

                    match check(addr, data, m, n) {
                        Ok(()) => {
                            assert!(all, "{ctx:#x?}");
                            accepted += 1;
                        }
                        Err(PackedPtrError::UnsafeConfig) => {
                            assert!(!(valid && spec::addr_fits(a, m)), "{ctx:#x?}");
                            rejected[0] += 1;
                        }
                        Err(PackedPtrError::UnalignedAddress) => {
                            assert!(!spec::addr_aligned(a, n), "{ctx:#x?}");
                            rejected[1] += 1;
                        }
                        Err(PackedPtrError::DataOverflow) => {
                            assert!(!spec::data_fits(d, m, n), "{ctx:#x?}");
                            rejected[2] += 1;
                        }
                    }
                }
            }
        }

        // Every branch of the spec was exercised
        assert!(accepted > 0);
        assert!(rejected.iter().all(|&count| count > 0));
    }

    /// The converse of the `Ok` case: each `Err` contradicts one of the conditions, so if they all
    /// hold the result must be `Ok`.
    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn check_accepts_everything_the_spec_allows() {
        for (m, n) in valid_configs() {
            for addr in values().map(|v| clean(v, m, n)) {
                for data in values().map(|v| fit(v, m, n)) {
                    assert_eq!(
                        check(addr, data, m, n),
                        Ok(()),
                        "addr = {addr:#x}, data = {data:#x}, m = {m}, n = {n}"
                    );
                }
            }
        }
    }

    // ---------------------------------------------------------------------------------------------
    // bits.pack_unpack_roundtrip: check a d m n = Ok → unpack (pack a d m n) = (a, d)
    // ---------------------------------------------------------------------------------------------

    #[test]
    fn roundtrip_examples() {
        for (addr, data, m, n) in [
            (0, 0, 0, 0),
            (usize::MAX, 0, 0, 0),
            (0x1000, 0b1011_0101, 8, 3),
            (0x1000, 2047, 8, 3),
            ((usize::MAX >> 8) - 7, 2047, 8, 3),
            (0, usize::MAX, 0, BITS),
            (0, usize::MAX, BITS, 0),
            (0, usize::MAX, 8, BITS - 8),
            (0, usize::MAX / 3, BITS / 2, BITS / 2),
            (1 << (BITS / 2), usize::MAX >> 1, BITS / 2 - 1, BITS / 2),
        ] {
            assert_eq!(check(addr, data, m, n), Ok(()));
            let packed = pack_addr(addr, data, m, n);
            assert_eq!(unpack_addr(packed, m, n), addr);
            assert_eq!(unpack_data(packed, m, n), data);
        }
    }

    /// Whatever `check` accepts roundtrips, over every input in the grid (valid or not).
    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn roundtrip_whenever_check_passes() {
        let mut accepted = 0usize;

        for (m, n) in configs() {
            for addr in values() {
                for data in values() {
                    if check(addr, data, m, n).is_err() {
                        continue;
                    }
                    accepted += 1;

                    let packed = pack_addr(addr, data, m, n);
                    assert_eq!(
                        (unpack_addr(packed, m, n), unpack_data(packed, m, n)),
                        (addr, data),
                        "addr = {addr:#x}, data = {data:#x}, m = {m}, n = {n}"
                    );
                }
            }
        }

        assert!(accepted > 0);
    }

    /// Roundtrip over inputs constructed to satisfy the spec, so that every valid configuration is
    /// covered with many addresses and data values.
    #[test]
    #[cfg_attr(miri, ignore = "too slow under Miri")]
    fn roundtrip_for_every_valid_config() {
        for m in 0..=BITS {
            for n in 0..=BITS - m {
                for v in values().step_by(7) {
                    let addr = clean(v, m, n);
                    let data = fit(v.rotate_left(13) ^ (usize::MAX / 3), m, n);
                    assert_eq!(check(addr, data, m, n), Ok(()));

                    let packed = pack_addr(addr, data, m, n);
                    assert_eq!(
                        (unpack_addr(packed, m, n), unpack_data(packed, m, n)),
                        (addr, data),
                        "addr = {addr:#x}, data = {data:#x}, m = {m}, n = {n}"
                    );
                }
            }
        }
    }
}
