import Aeneas
import PackedPtr.Code.PackedPtr
import PackedPtr.Defs
import PackedPtr.Lemmas
open Aeneas Aeneas.Std Result

namespace PackedPtr

@[step]
theorem bits.lsb_bits_mask_spec (n: Usize) :
    bits.lsb_bits_mask n ⦃ r => r.val = 2 ^ (min n.val Usize.numBits) - 1 ⦄ := by
  unfold bits.lsb_bits_mask

  step as ⟨i, hi⟩

  -- Prove that i.val = Usize.numBits
  have hi : i.val = Usize.numBits := by scalar_tac

  split
  · -- n ≥ BITS => usize::MAX
    rename_i h
    have hn : Usize.numBits ≤ n.val := by scalar_tac
    simp [core.num.Usize.MAX, Usize.max_def, Nat.min_eq_right hn]
  · -- n < BITS => 2^n - 1
    rename_i h

    -- n < BITS ∴ 2^n < 2^BITS
    have hn : n.val < Usize.numBits := by scalar_tac
    have hpow : 2 ^ n.val < 2 ^ Usize.numBits := Nat.pow_lt_pow_right (by decide) hn

    step as ⟨i₁, hi₁, _⟩

    -- Prove that i₁ <<< n equals 2^n
    have hi₁ : i₁.val = 2 ^ n.val := by
      rw [hi₁, Nat.shiftLeft_eq, one_mul, Usize.size_def]
      exact Nat.mod_eq_of_lt hpow

    -- Prove that i₁ is at least 1
    have : 1 ≤ i₁.val := by rw [hi₁]; exact Nat.one_le_two_pow

    step as ⟨i₂, hi₂⟩
    rw [Nat.min_eq_left hn.le, hi₂, hi₁]

@[step]
theorem bits.msb_bits_mask_spec (m : Usize) :
    bits.msb_bits_mask m ⦃ r => r.val = 2 ^ (Usize.numBits) - 2 ^ (Usize.numBits - min m.val Usize.numBits) ⦄ := by
  unfold bits.msb_bits_mask

  split
  · -- m == 0 => 0
    rename_i h
    subst h

    -- Remove ok
    simp only [WP.spec_ok]

    -- 0 = 2 ^ x - 2 ^ (x - min(0, x))
    simp

  · -- m != 0 => 2^BITS - 2^(BITS - min(m, BITS))
    rename_i h
    simp at h

    step as ⟨i, hi⟩

    -- i = Usize.numBits
    have hi : i.val = Usize.numBits := by scalar_tac

    -- simplify out lift
    simp only [lift, bind_ok]

    -- Prove that i |- m = BITS - min(m, BITS)
    have hs : (core.num.Usize.saturating_sub i m).val = Usize.numBits - min m.val Usize.numBits := by
      rw [usize_saturating_sub_val, hi]
      omega

    -- Prove that saturating_sub i m < Usize.numBits (shift precondition)
    have : (core.num.Usize.saturating_sub i m).val < Usize.numBits := by
      have := UScalarTy.Usize.numBits_nonzero
      rw [hs, Usize.numBits]
      omega

    step as ⟨i₁, hi₁⟩

    -- Substitute hs into hi₁
    have hi₁ : i₁.val = Usize.max <<< (Usize.numBits - min m.val Usize.numBits) % Usize.size := by rwa [← hs]

    -- Convert to ℕ arithmetic
    rw [hi₁, Usize.max_def, Usize.size_def, Nat.shiftLeft_eq]

    -- Prove that BITS - min(m, BITS) ≤ BITS
    have hk : Usize.numBits - min (↑m) Usize.numBits ≤ Usize.numBits := Nat.sub_le _ _

    -- Rewrite in terms of k and n for easier manipulation
    generalize Usize.numBits - min (↑m) Usize.numBits = k at *
    generalize Usize.numBits = n at *

    have hb : 1 ≤ 2 ^ k := Nat.one_le_two_pow
    have ha : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    have hba : 2 ^ k ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hk

    -- Rewrite to allow elimination of mod 2 ^ n
    have key : (2 ^ n - 1) * 2 ^ k = (2 ^ n - 2 ^ k) + 2 ^ n * (2 ^ k - 1) := by
      zify [hb, ha, hba]
      ring

    -- Simplify
    rw [key, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]


theorem bits.bits_mask_disjoint (m n : Usize) (h : valid_config m.val n.val) :
    (do
      let a ← bits.lsb_bits_mask n
      let b ← bits.msb_bits_mask m
      ok (a.val &&& b.val)) ⦃ r => r = 0 ⦄ := by
  unfold valid_config at h

  step as ⟨a, ha⟩
  step as ⟨b, hb⟩

  have hn : n.val ≤ Usize.numBits := Nat.le_of_add_left_le h;
  have hm : m.val ≤ Usize.numBits := Nat.le_of_add_right_le h;

  have ha' : a.val = 2 ^ n.val - 1 := by
    rw [<- Nat.min_eq_left hn]
    exact ha

  have hb' : b.val = 2 ^ Usize.numBits - 2 ^ (Usize.numBits - m.val) := by
    rw [<- Nat.min_eq_left hm]
    exact hb

  rw [ha', hb', Nat.and_comm, Nat.and_two_pow_sub_one_eq_mod]

  -- Per theorem, modulo == 0, so 2^n divides b
  apply Nat.mod_eq_zero_of_dvd

  have hk : n.val ≤ Usize.numBits - m.val := by omega;
  have hN : 2 ^ (Usize.numBits - ↑m) ∣ 2 ^ Usize.numBits := Nat.pow_dvd_pow 2 (Nat.sub_le _ _)

  exact Nat.dvd_trans (Nat.pow_dvd_pow 2 hk) (Nat.dvd_sub hN (Nat.dvd_refl _))

theorem bits.pack_addr_spec (a d m n : Usize)
    (h : valid_config m.val n.val)
    (hc : clean_addr a.val m.val n.val) :
    bits.pack_addr a d m n ⦃ r => r.val = pack a.val d.val m.val n.val ⦄ := by
  unfold bits.pack_addr

  -- Unfold the safety conditions
  unfold valid_config at h
  obtain ⟨hlo, hhi⟩ := hc
  unfold addr_aligned at hlo
  unfold addr_fits at hhi

  -- BITS < usize::MAX, so m + n doesn't overflow
  have hmax : m.val + n.val ≤ Usize.max := by
    have : Usize.numBits < Usize.max := by
      rw [Usize.max_def, Usize.numBits, UScalarTy.Usize_numBits_eq]
      cases System.Platform.numBits_eq <;> simp [*]
    omega

  -- debug_assert!(m + n <= BITS)
  step as ⟨sum, hsum⟩ -- m + n
  step as ⟨bits, hbits⟩ -- BITS as usize
  have hbits : bits.val = Usize.numBits := by rw [hbits]; scalar_tac
  step as ⟨_⟩ -- massert (m + n ≤ BITS)

  split
  · -- m == 0
    rename_i hm
    have hm : m.val = 0 := by simp [hm]

    step as ⟨l, hl⟩
    simp [lift]

    have hl : l.val = 2 ^ n.val - 1 := by rw [hl, Nat.min_eq_left (by omega)]

    unfold pack

    rw [hm, hl, Nat.and_two_pow_sub_one_eq_mod]
    simp only [Nat.pow_zero, Nat.sub_zero, Nat.mod_one, Nat.zero_mul, Nat.add_zero]

    have ha : a.val = 2 ^ n.val * (a.val / 2 ^ n.val) := by
      have := Nat.div_add_mod a.val (2 ^ n.val)
      rw [hlo, Nat.add_zero] at this
      exact this.symm

    rw [ha]
    exact (Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)) _).symm
  · -- m != 0
    rename_i hm
    simp at hm

    -- m ≥ 1 ∴ n < BITS (shift precondition)
    have hn : n.val < Usize.numBits := by omega

    step as ⟨s, hs⟩ -- data >> n
    step as ⟨b, hb⟩ -- BITS as usize
    step as ⟨k, hk⟩ -- BITS - m
    step as ⟨u, hu⟩ -- (data >> n) << (BITS - m)
    step as ⟨l, hl⟩ -- lsb_bits_mask n
    simp [lift]

    have hb : b.val = Usize.numBits := by rw [hb]; scalar_tac
    have hk : k.val = Usize.numBits - m.val := by rw [hk, hb]
    have hl : l.val = 2 ^ n.val - 1 := by rw [hl, Nat.min_eq_left hn.le]

    -- Truncating the shift to BITS keeps exactly the low m bits of data / 2^n
    have hu : u.val = d.val / 2 ^ n.val % 2 ^ m.val * 2 ^ (Usize.numBits - m.val) := by
      rw [hu, hs, hk, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Usize.size_def]
      have : 2 ^ Usize.numBits = 2 ^ m.val * 2 ^ (Usize.numBits - m.val) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [this, Nat.mul_mod_mul_right]

    unfold pack
    rw [hu, hl, Nat.and_two_pow_sub_one_eq_mod]
    generalize d.val / 2 ^ n.val % 2 ^ m.val = x

    -- addr < 2^(BITS - m), so addr | upper = addr + upper
    have h1 : a.val ||| x * 2 ^ (Usize.numBits - m.val)
        = a.val + x * 2 ^ (Usize.numBits - m.val) := by
      rw [Nat.or_comm, Nat.mul_comm, Nat.add_comm]
      exact (Nat.two_pow_add_eq_or_of_lt hhi _).symm

    -- 2^n divides addr + upper, so | lower is also addition
    obtain ⟨q, hq⟩ : 2 ^ n.val ∣ a.val + x * 2 ^ (Usize.numBits - m.val) :=
      Nat.dvd_add (Nat.dvd_of_mod_eq_zero hlo)
        (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 (by omega)) _)

    rw [h1, Nat.add_right_comm, hq]
    exact (Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)) _).symm

@[step]
theorem bits.unpack_addr_spec (p m n : Usize)
    (h : valid_config m.val n.val) :
    bits.unpack_addr p m n ⦃ r => r.val = PackedPtr.unpack_addr p.val m.val n.val ⦄ := by
  unfold bits.unpack_addr
  unfold valid_config at h

  have hn : n.val ≤ Usize.numBits := Nat.le_of_add_left_le h
  have hm : m.val ≤ Usize.numBits := Nat.le_of_add_right_le h

  -- Bitwise NOT on usize flips all BITS bits
  have hnot : ∀ x : Usize, (~~~x).val = 2 ^ Usize.numBits - 1 - x.val := by
    intro x
    simp only [UScalar.val, UScalar.bv_not, BitVec.toNat_not, Usize.numBits]

  step as ⟨hi, hhi⟩ -- msb_bits_mask m
  step as ⟨nhi, hnhi⟩ -- !msb_bits_mask m
  step as ⟨x, hx⟩ -- packed & !msb_bits_mask m
  step as ⟨lo, hlo⟩ -- lsb_bits_mask n
  step as ⟨nlo, hnlo⟩ -- !lsb_bits_mask n

  -- Convert to ℕ
  simp only [UScalar.val_and]
  rw [hx, UScalar.val_and, hnhi, hnlo, hnot, hnot, hhi, hlo,
    Nat.min_eq_left hm, Nat.min_eq_left hn]
  unfold PackedPtr.unpack_addr

  -- !msb_mask = 2^(BITS - m) - 1, so the first AND keeps the low BITS - m bits
  have hk : 2 ^ (Usize.numBits - m.val) ≤ 2 ^ Usize.numBits :=
    Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
  have h1 : 2 ^ Usize.numBits - 1 - (2 ^ Usize.numBits - 2 ^ (Usize.numBits - m.val))
      = 2 ^ (Usize.numBits - m.val) - 1 := by omega
  rw [h1, Nat.and_two_pow_sub_one_eq_mod]

  -- The remaining value still fits in BITS bits
  have hy : p.val % 2 ^ (Usize.numBits - m.val) < 2 ^ Usize.numBits :=
    lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) hk
  generalize p.val % 2 ^ (Usize.numBits - m.val) = y at hy

  -- !lsb_mask = 2^BITS - 2^n
  have hpn : 1 ≤ 2 ^ n.val := Nat.one_le_two_pow
  have h2 : 2 ^ Usize.numBits - 1 - (2 ^ n.val - 1) = 2 ^ Usize.numBits - 2 ^ n.val := by omega
  rw [h2]

  -- Clearing the low n bits is rounding down to a multiple of 2^n
  exact and_msb_mask_eq_div_mul _ _ _ hn hy

@[step]
theorem bits.unpack_data_spec (p m n : Usize)
    (h : valid_config m.val n.val) :
    bits.unpack_data p m n ⦃ r => r.val = PackedPtr.unpack_data p.val m.val n.val ⦄ := by
  unfold bits.unpack_data
  unfold valid_config at h

  have hn : n.val ≤ Usize.numBits := Nat.le_of_add_left_le h
  have hm : m.val ≤ Usize.numBits := Nat.le_of_add_right_le h

  -- packed fits in a usize
  have hp : p.val < 2 ^ Usize.numBits := by scalar_tac

  -- BITS < usize::MAX, so m + n doesn't overflow
  have hmax : m.val + n.val ≤ Usize.max := by
    have : Usize.numBits < Usize.max := by
      rw [Usize.max_def, Usize.numBits, UScalarTy.Usize_numBits_eq]
      cases System.Platform.numBits_eq <;> simp [*]
    omega

  -- debug_assert!(m + n <= BITS)
  step as ⟨sum, hsum⟩ -- m + n
  step as ⟨bits, hbits⟩ -- BITS as usize
  have hbits : bits.val = Usize.numBits := by rw [hbits]; scalar_tac
  step as ⟨_⟩ -- massert (m + n ≤ BITS)

  step as ⟨l, hl⟩ -- lsb_bits_mask n
  step as ⟨lower, hlower⟩ -- packed & lsb_bits_mask n

  -- lower is the low n bits of packed
  have hlower : lower.val = p.val % 2 ^ n.val := by
    rw [hlower, UScalar.val_and, hl, Nat.min_eq_left hn, Nat.and_two_pow_sub_one_eq_mod]

  unfold PackedPtr.unpack_data

  split
  · -- m == 0 => lower
    rename_i hm0
    have hm0 : m.val = 0 := by simp [hm0]
    simp only [WP.spec_ok]

    -- packed < 2^BITS, so there are no upper bits
    rw [hlower, hm0, Nat.sub_zero, Nat.div_eq_of_lt hp, Nat.zero_mul, Nat.add_zero]
  · -- m != 0 => lower | (upper >> (BITS - m - n))
    rename_i hm0
    simp at hm0

    step as ⟨hi, hhi⟩ -- msb_bits_mask m
    step as ⟨upper, hupper⟩ -- packed & msb_bits_mask m
    step as ⟨b, hb⟩ -- BITS as usize
    step as ⟨k, hk⟩ -- BITS - m
    step as ⟨s, hs⟩ -- BITS - m - n
    step as ⟨u, hu⟩ -- upper >> (BITS - m - n)

    have hb : b.val = Usize.numBits := by rw [hb]; scalar_tac
    have hk : k.val = Usize.numBits - m.val := by rw [hk, hb]
    have hs : s.val = Usize.numBits - m.val - n.val := by rw [hs, hk]

    -- Keeping only the upper m bits is rounding down to a multiple of 2^(BITS - m)
    have hmask : p.val &&& (2 ^ Usize.numBits - 2 ^ (Usize.numBits - m.val))
        = p.val / 2 ^ (Usize.numBits - m.val) * 2 ^ (Usize.numBits - m.val) :=
      and_msb_mask_eq_div_mul _ _ _ (Nat.sub_le _ _) hp

    -- Shifting right by BITS - m - n leaves the upper m bits starting at bit n
    have hu : u.val = p.val / 2 ^ (Usize.numBits - m.val) * 2 ^ n.val := by
      rw [hu, hupper, UScalar.val_and, hhi, Nat.min_eq_left hm, hmask, hs,
        Nat.shiftRight_eq_div_pow]
      have : 2 ^ (Usize.numBits - m.val) = 2 ^ n.val * 2 ^ (Usize.numBits - m.val - n.val) := by
        rw [← Nat.pow_add]; congr 1; omega
      rw [this, ← Nat.mul_assoc, Nat.mul_div_cancel _ (Nat.two_pow_pos _), ← this]

    rw [UScalar.val_or, hlower, hu]
    generalize p.val / 2 ^ (Usize.numBits - m.val) = q

    -- lower < 2^n and 2^n divides the shifted upper bits, so | is addition
    rw [Nat.or_comm, Nat.mul_comm, Nat.add_comm]
    exact (Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (Nat.two_pow_pos _)) _).symm

-- Unpacking the address of a packed value gives back the original address
theorem unpack_addr_pack (a d m n : Nat)
    (h : valid_config m n)
    (hc : clean_addr a m n) :
    unpack_addr (pack a d m n) m n = a := by
  -- The lower n bits of data are below 2^n
  have hr : d % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos _)

  -- addr + lower doesn't reach the upper m bits
  have hlt := clean_addr_add_lt a (d % 2 ^ n) m n h hc hr

  -- addr = 2^n * c
  obtain ⟨c, rfl⟩ : 2 ^ n ∣ a := Nat.dvd_of_mod_eq_zero hc.1

  unfold pack unpack_addr

  -- The modulo drops the upper bits, the division drops the lower bits
  rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlt, Nat.mul_add_div (Nat.two_pow_pos _),
    Nat.div_eq_of_lt hr, Nat.add_zero, Nat.mul_comm]

-- Unpacking the data of a packed value gives back the original data
theorem unpack_data_pack (a d m n : Nat)
    (h : valid_config m n)
    (hc : clean_addr a m n)
    (hd : data_fits d m n) :
    unpack_data (pack a d m n) m n = d := by
  -- The lower n bits of data are below 2^n
  have hr : d % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos _)

  -- addr + lower doesn't reach the upper m bits
  have hlt := clean_addr_add_lt a (d % 2 ^ n) m n h hc hr

  unfold valid_config at h
  unfold data_fits at hd
  unfold pack unpack_data

  -- data < 2^(m + n), so data / 2^n already fits in m bits
  have hx : d / 2 ^ n < 2 ^ m := by
    apply Nat.div_lt_of_lt_mul
    rwa [← Nat.pow_add, Nat.add_comm]
  rw [Nat.mod_eq_of_lt hx]
  generalize hxd : d / 2 ^ n = x

  -- 2^n divides addr + upper, so the low n bits of packed are the low n bits of data
  have h1 : (a + d % 2 ^ n + x * 2 ^ (Usize.numBits - m)) % 2 ^ n = d % 2 ^ n := by
    obtain ⟨z, hz⟩ : 2 ^ n ∣ a + x * 2 ^ (Usize.numBits - m) :=
      Nat.dvd_add (Nat.dvd_of_mod_eq_zero hc.1)
        (Nat.dvd_mul_left_of_dvd (Nat.pow_dvd_pow 2 (by omega)) _)
    rw [Nat.add_right_comm, hz, Nat.mul_add_mod, Nat.mod_mod]

  -- addr + lower < 2^(BITS - m), so the upper m bits of packed are data / 2^n
  have h2 : (a + d % 2 ^ n + x * 2 ^ (Usize.numBits - m)) / 2 ^ (Usize.numBits - m) = x := by
    rw [Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.div_eq_of_lt hlt, Nat.zero_add]

  rw [h1, h2, ← hxd]
  exact Nat.mod_add_div' d (2 ^ n)

@[step]
theorem bits.is_unsafe_config_spec (a m n : Usize) :
    bits.is_unsafe_config a m n ⦃ r => r = true ↔ ¬(valid_config m.val n.val ∧ addr_fits a.val m.val) ⦄ := by
  unfold bits.is_unsafe_config

  -- Unsafe ↔ BITS < m + n ∨ 2^(BITS - m) ≤ addr
  unfold valid_config addr_fits
  simp only [not_and_or, Nat.not_le, Nat.not_lt]

  -- Remove lift
  simp only [lift, bind_ok]

  -- BITS < usize::MAX (so a saturated sum still exceeds BITS)
  have hmax : Usize.numBits < Usize.max := by
    rw [Usize.max_def, Usize.numBits, UScalarTy.Usize_numBits_eq]
    cases System.Platform.numBits_eq <;> simp [*]

  -- BITS as usize = BITS
  have hi : (UScalar.cast UScalarTy.Usize core.num.Usize.BITS).val = Usize.numBits := by
    scalar_tac

  -- Convert the comparison to ℕ arithmetic
  have hgt : (core.num.Usize.saturating_add m n > UScalar.cast UScalarTy.Usize core.num.Usize.BITS)
      ↔ Usize.numBits < m.val + n.val := by
    have := UScalar.lt_equiv (UScalar.cast UScalarTy.Usize core.num.Usize.BITS)
      (core.num.Usize.saturating_add m n)
    rw [usize_saturating_add_val, hi] at this
    rw [gt_iff_lt, this]

    by_cases hs : m.val + n.val ≤ Usize.max
    · -- No saturation => the sum is exact
      rw [Nat.min_eq_right hs]
    · -- Saturation => both sides exceed BITS
      have hs : Usize.max < m.val + n.val := Nat.lt_of_not_le hs
      rw [Nat.min_eq_left hs.le]
      exact ⟨fun _ => lt_trans hmax hs, fun _ => hmax⟩

  split
  · -- m + n > BITS => true
    rename_i h
    simp only [WP.spec_ok, true_iff]
    exact Or.inl (hgt.mp h)
  · -- m + n ≤ BITS => addr & msb_bits_mask(m) != 0
    rename_i h
    have hmn : m.val + n.val ≤ Usize.numBits := by
      have := mt hgt.mpr h
      omega

    step as ⟨k, hk⟩ -- msb_bits_mask m

    -- Convert the `!= 0` test to ℕ
    simp

    -- m ≤ BITS, so the mask covers exactly the upper m bits
    have hk : k.val = 2 ^ Usize.numBits - 2 ^ (Usize.numBits - m.val) := by
      rw [hk, Nat.min_eq_left (by omega)]

    -- addr fits in a usize
    have ha : a.val < 2 ^ Usize.numBits := by scalar_tac

    -- addr & mask = 0 ↔ addr < 2^(BITS - m)
    rw [hk, and_msb_mask_eq_zero_iff _ _ _ (Nat.sub_le _ _) ha]
    omega

@[step]
theorem bits.is_unaligned_addr_spec (a n : Usize) :
    bits.is_unaligned_addr a n ⦃ r => r = true ↔ ¬addr_aligned a.val n.val ⦄ := by
  unfold bits.is_unaligned_addr
  unfold addr_aligned

  step as ⟨l, hl⟩ -- lsb_bits_mask n

  -- Remove lift & convert the `!= 0` test to ℕ
  simp [lift]

  -- addr & (2^k - 1) = addr % 2^k, where k = min(n, BITS)
  rw [hl, Nat.and_two_pow_sub_one_eq_mod]

  -- addr fits in a usize
  have ha : a.val < 2 ^ Usize.numBits := by scalar_tac

  by_cases hn : n.val ≤ Usize.numBits
  · -- n ≤ BITS => mask is exactly 2^n - 1
    rw [Nat.min_eq_left hn]
  · -- n > BITS => mask is usize::MAX, and addr < 2^BITS ≤ 2^n
    have hn : Usize.numBits ≤ n.val := by omega

    -- Both moduli are larger than addr, so both sides reduce to addr
    rw [Nat.min_eq_right hn, Nat.mod_eq_of_lt ha,
      Nat.mod_eq_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) hn))]

@[step]
theorem bits.is_unsafe_data_spec (d m n : Usize) :
    bits.is_unsafe_data d m n ⦃ r => r = true ↔ ¬data_fits d.val m.val n.val ⦄ := by
  unfold bits.is_unsafe_data

  -- Unsafe ↔ 2^(m + n) ≤ data
  unfold data_fits
  simp only [Nat.not_lt]

  -- Remove lift
  simp only [lift, bind_ok]

  -- data fits in a usize, and BITS < 2^BITS
  have hd : d.val < 2 ^ Usize.numBits := by scalar_tac
  have hw : Usize.numBits < 2 ^ Usize.numBits := Nat.lt_two_pow_self
  have hbits : UScalarTy.Usize.numBits = Usize.numBits := by rw [Usize.numBits]

  -- Leading zeros in terms of data's value
  have hlz := usize_leading_zeros_val d

  -- leading_zeros ≤ BITS (subtraction precondition)
  have hle : (core.num.Usize.leading_zeros d).val ≤ Usize.numBits := by
    rw [hlz]
    split <;> omega

  step as ⟨i1, hi1⟩ -- BITS - leading_zeros

  -- State i1 in terms of BITS
  replace hi1 : i1.val = Usize.numBits - (core.num.Usize.leading_zeros d).val := by
    rw [hi1, hbits]

  -- Casting i1 from u32 to usize doesn't truncate it
  have hc : (UScalar.cast UScalarTy.Usize i1).val = i1.val := by
    rw [UScalar.cast_val_eq, hbits]
    exact Nat.mod_eq_of_lt (by omega)

  -- Convert the comparison to ℕ arithmetic
  have hgt : (UScalar.cast UScalarTy.Usize i1 > core.num.Usize.saturating_add m n)
      ↔ min (2 ^ Usize.numBits - 1) (m.val + n.val)
        < Usize.numBits - (core.num.Usize.leading_zeros d).val := by
    have := UScalar.lt_equiv (core.num.Usize.saturating_add m n) (UScalar.cast UScalarTy.Usize i1)
    rw [usize_saturating_add_val, hc, hi1, Usize.max_def] at this
    exact this

  rw [decide_eq_true_iff, hgt, hlz]

  split
  · -- data == 0 => no bits used, and 2^(m + n) ≥ 1 > data
    rename_i h0
    have := Nat.two_pow_pos (m.val + n.val)
    omega
  · -- data != 0 => data uses log2(data) + 1 bits
    rename_i hne

    -- data < 2^BITS ∴ log2(data) < BITS
    have hlog : Nat.log 2 d.val < Usize.numBits :=
      (Nat.log_lt_iff_lt_pow (by decide) hne).mpr hd

    -- 2^(m + n) ≤ data ↔ m + n ≤ log2(data)
    rw [← Nat.le_log_iff_pow_le (by decide) hne]
    omega

@[step]
theorem bits.check_spec (a d m n : Usize) :
    bits.check a d m n ⦃ r =>
      match r with
      | .Ok () => valid_config m.val n.val ∧ clean_addr a.val m.val n.val
          ∧ data_fits d.val m.val n.val
      | .Err .UnsafeConfig => ¬(valid_config m.val n.val ∧ addr_fits a.val m.val)
      | .Err .UnalignedAddress => ¬addr_aligned a.val n.val
      | .Err .DataOverflow => ¬data_fits d.val m.val n.val ⦄ := by
  unfold bits.check

  step as ⟨b, hb⟩ -- is_unsafe_config

  split
  · -- Unsafe config => Err(UnsafeConfig)
    rename_i h
    simp only [WP.spec_ok]
    exact hb.mp h
  · -- Safe config: m + n ≤ BITS and addr fits below the upper m bits
    rename_i h
    have hcfg : valid_config m.val n.val ∧ addr_fits a.val m.val :=
      Classical.not_not.mp (mt hb.mpr h)

    step as ⟨b1, hb1⟩ -- is_unaligned_addr

    split
    · -- Unaligned address => Err(UnalignedAddress)
      rename_i h1
      simp only [WP.spec_ok]
      exact hb1.mp h1
    · -- Aligned address, so addr is clean
      rename_i h1
      have hc : clean_addr a.val m.val n.val :=
        ⟨Classical.not_not.mp (mt hb1.mpr h1), hcfg.2⟩

      step as ⟨b2, hb2⟩ -- is_unsafe_data

      split
      · -- Data doesn't fit in m + n bits => Err(DataOverflow)
        rename_i h2
        simp only [WP.spec_ok]
        exact hb2.mp h2
      · -- Data fits => Ok(())
        rename_i h2
        simp only [WP.spec_ok]
        exact ⟨hcfg.1, hc, Classical.not_not.mp (mt hb2.mpr h2)⟩

-- End-to-end: if `check` accepts the inputs, packing never panics and
-- unpacking the packed value gives back the original address and data
theorem bits.pack_unpack_roundtrip (a d m n : Usize)
    (h : bits.check a d m n = ok (core.result.Result.Ok ())) :
    (do
      let p ← bits.pack_addr a d m n
      let a' ← bits.unpack_addr p m n
      let d' ← bits.unpack_data p m n
      ok (a', d')) ⦃ r => r = (a, d) ⦄ := by
  -- `check` returned Ok, so all the safety conditions hold
  have hs := bits.check_spec a d m n
  rw [h] at hs
  simp only [WP.spec_ok] at hs
  obtain ⟨hcfg, hc, hd⟩ := hs

  step with bits.pack_addr_spec as ⟨p, hp⟩ -- pack_addr
  step as ⟨a', ha'⟩ -- unpack_addr
  step as ⟨d', hd'⟩ -- unpack_data

  -- The Rust functions match the model, and the model round-trips
  have ha : a'.val = a.val := by
    rw [ha', hp]
    exact unpack_addr_pack _ _ _ _ hcfg hc
  have hd : d'.val = d.val := by
    rw [hd', hp]
    exact unpack_data_pack _ _ _ _ hcfg hc hd

  -- Equal values => equal usizes
  exact ⟨UScalar.eq_of_val_eq ha, UScalar.eq_of_val_eq hd⟩

end PackedPtr
