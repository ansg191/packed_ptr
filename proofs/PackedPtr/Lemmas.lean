import Aeneas
import PackedPtr.Defs
open Aeneas Aeneas.Std

namespace PackedPtr

-- Saturating subtraction on usize is subtraction on ℕ
theorem usize_saturating_sub_val (x y : Usize) :
    (core.num.Usize.saturating_sub x y).val = x.val - y.val := by
  simp only [core.num.Usize.saturating_sub, UScalar.saturating_sub, UScalar.val, BitVec.toNat_ofNat, Nat.zero_max]
  apply Nat.mod_eq_of_lt
  have := x.bv.isLt
  omega

-- Saturating addition on usize is addition on ℕ, clamped to usize::MAX
theorem usize_saturating_add_val (x y : Usize) :
    (core.num.Usize.saturating_add x y).val = min Usize.max (x.val + y.val) := by
  simp only [core.num.Usize.saturating_add, UScalar.saturating_add, UScalar.val,
    BitVec.toNat_ofNat, UScalar.max_USize_eq]

  -- min(MAX, x + y) ≤ MAX < 2^BITS, so the truncation is a no-op
  apply Nat.mod_eq_of_lt
  have : Usize.max < 2 ^ UScalarTy.Usize.numBits := by
    rw [Usize.max_def, Usize.numBits]
    have := Nat.two_pow_pos UScalarTy.Usize.numBits
    omega
  exact lt_of_le_of_lt (Nat.min_le_left _ _) this

-- Leading zeros of a usize in terms of its value in ℕ:
-- a non-zero x occupies log2(x) + 1 bits, the rest are leading zeros
theorem usize_leading_zeros_val (x : Usize) :
    (core.num.Usize.leading_zeros x).val
      = if x.val = 0 then Usize.numBits else Usize.numBits - Nat.log 2 x.val - 1 := by
  -- BITS fits in a u32 (leading_zeros returns u32)
  have hw32 : System.Platform.numBits < 2 ^ 32 := by
    cases System.Platform.numBits_eq <;> simp [*]

  -- The underlying bitvector is 0 iff its value is 0
  have hz : x.bv = 0 ↔ x.val = 0 := by
    constructor
    · intro h; change x.bv.toNat = 0; rw [h]; rfl
    · intro h; exact BitVec.eq_of_toNat_eq h

  -- Restate the bitvector definition in terms of x's value
  have hdef : BitVec.leadingZeros x.bv
      = if x.val = 0 then System.Platform.numBits
        else System.Platform.numBits - Nat.log 2 x.val - 1 := by
    unfold BitVec.leadingZeros
    simp only [hz]
    rfl

  -- leading_zeros ≤ BITS
  have hle : BitVec.leadingZeros x.bv ≤ System.Platform.numBits := by
    rw [hdef]
    split <;> omega

  -- Storing the count in a u32 doesn't truncate it
  rw [Usize.numBits, UScalarTy.Usize_numBits_eq, ← hdef]
  simp only [core.num.Usize.leading_zeros, UScalar.val]
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt hle hw32)

-- An address has none of the bits [j, b) set iff it fits in the low j bits
theorem and_msb_mask_eq_zero_iff (a b j : Nat) (hj : j ≤ b) (ha : a < 2 ^ b) :
    a &&& (2 ^ b - 2 ^ j) = 0 ↔ a < 2 ^ j := by
  -- The mask is b - j ones shifted left by j
  have hmask : 2 ^ b - 2 ^ j = (2 ^ (b - j) - 1) <<< j := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, ← Nat.pow_add, Nat.sub_add_cancel hj, Nat.one_mul]

  rw [hmask]

  constructor
  · -- a & mask = 0 => a < 2^j (by contradiction)
    intro h
    apply Nat.lt_of_not_le
    intro hle

    -- 2^j ≤ a ∴ a has some bit i ≥ j set
    obtain ⟨i, hi, hbit⟩ := Nat.exists_ge_and_testBit_of_ge_two_pow hle

    -- a < 2^b ∴ i < b
    have hib : i < b := by
      apply Nat.lt_of_not_le
      intro hbi
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hbi))
      rw [this] at hbit
      exact absurd hbit (by decide)

    -- Bit i is set in both a and the mask, so it is set in a & mask
    have : (a &&& (2 ^ (b - j) - 1) <<< j).testBit i = true := by
      rw [Nat.testBit_and, hbit, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one]
      simp
      omega

    -- But a & mask = 0 has no bits set
    rw [h, Nat.zero_testBit] at this
    exact absurd this (by decide)
  · -- a < 2^j => a & mask = 0 (bit by bit)
    intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.zero_testBit]

    by_cases hi : j ≤ i
    · -- i ≥ j => a < 2^j ≤ 2^i, so bit i of a is unset
      rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) hi))]
      simp
    · -- i < j => bit i of the mask is unset
      simp [hi]

-- Keeping only the bits [j, b) of a value below 2^b is rounding down to a multiple of 2^j
theorem and_msb_mask_eq_div_mul (a b j : Nat) (hj : j ≤ b) (ha : a < 2 ^ b) :
    a &&& (2 ^ b - 2 ^ j) = a / 2 ^ j * 2 ^ j := by
  -- The mask is b - j ones shifted left by j
  have hmask : 2 ^ b - 2 ^ j = (2 ^ (b - j) - 1) <<< j := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, ← Nat.pow_add, Nat.sub_add_cancel hj, Nat.one_mul]

  rw [hmask]

  -- Bit by bit
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_two_pow_sub_one,
    Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]

  by_cases hi : j ≤ i
  · -- i ≥ j => both sides are bit i of a (unset once i ≥ b)
    rw [Nat.sub_add_cancel hi]
    by_cases hib : i < b
    · simp [hi]
      omega
    · -- a < 2^b ≤ 2^i, so bit i of a is unset
      rw [Nat.testBit_lt_two_pow
        (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hib)))]
      simp
  · -- i < j => both sides are unset
    simp [hi]

-- A clean address plus any lower n bits still fits below the upper m bits
theorem clean_addr_add_lt (a r m n : Nat)
    (h : valid_config m n)
    (hc : clean_addr a m n)
    (hr : r < 2 ^ n) :
    a + r < 2 ^ (Usize.numBits - m) := by
  unfold valid_config at h
  obtain ⟨hlo, hhi⟩ := hc
  unfold addr_aligned at hlo
  unfold addr_fits at hhi

  -- addr = 2^n * c
  obtain ⟨c, rfl⟩ : 2 ^ n ∣ a := Nat.dvd_of_mod_eq_zero hlo

  -- 2^(BITS - m) = 2^n * 2^(BITS - m - n)
  have hK : 2 ^ (Usize.numBits - m) = 2 ^ n * 2 ^ (Usize.numBits - m - n) := by
    rw [← Nat.pow_add]; congr 1; omega
  rw [hK] at hhi ⊢

  -- c < 2^(BITS - m - n), so 2^n * c + r < 2^n * (c + 1) ≤ 2^(BITS - m)
  have hc : c < 2 ^ (Usize.numBits - m - n) :=
    Nat.lt_of_mul_lt_mul_left hhi
  calc 2 ^ n * c + r < 2 ^ n * c + 2 ^ n := by omega
    _ = 2 ^ n * (c + 1) := by ring
    _ ≤ 2 ^ n * 2 ^ (Usize.numBits - m - n) := Nat.mul_le_mul_left _ hc

end PackedPtr
