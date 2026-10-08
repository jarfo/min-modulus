import MinModulus.SILiftTransport

/-!
# The SI-lift sheet

Everything proved so far about the SI block lives at ONE modulus.  The
route item is a LIFT statement: the parent sits at stratum `(n, s)` and the
child at stratum `(n-1, s-1)`, and

    2 * (2 ^ (n-1) - 2 ^ (s-1)) = 2 ^ n - 2 ^ s,

so the child modulus is exactly half the parent's.  Writing `n = m + 2` and
`s = t + 1` (so `s ≥ 2` is `t ≥ 1`) keeps every subtraction truncation-free.

This file sets up that framework: the two moduli, the reduction ring
homomorphism between them, the sheet element — the unique nonzero element
killed by the reduction, which is its own negative — and the fact that the
kernel is exactly `{0, sheet}`.  A lift of a child entry is therefore
determined up to adding the sheet, which is what the sheet BITS record.
-/

namespace MinModulus

section Sheet

variable (m t : ℕ)

/-- Parent modulus: stratum `(m + 2, t + 1)`. -/
def siFull : ℕ := 2 ^ (m + 2) - 2 ^ (t + 1)

/-- Child modulus: stratum `(m + 1, t)`, exactly half the parent's. -/
def siHalf : ℕ := 2 ^ (m + 1) - 2 ^ t

variable {m t}

lemma siHalf_pos (hm : t ≤ m) : 0 < siHalf m t := by
  have h : (2 : ℕ) ^ t < 2 ^ (m + 1) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  unfold siHalf; omega

lemma siFull_eq_two_mul (hm : t ≤ m) : siFull m t = 2 * siHalf m t := by
  have hp1 : (2 : ℕ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
  have hp2 : (2 : ℕ) ^ (t + 1) = 2 * 2 ^ t := by ring
  have hle : (2 : ℕ) ^ t ≤ 2 ^ (m + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold siFull siHalf; omega

lemma siFull_pos (hm : t ≤ m) : 0 < siFull m t := by
  have := siHalf_pos hm
  rw [siFull_eq_two_mul hm]; omega

lemma siHalf_dvd (hm : t ≤ m) : siHalf m t ∣ siFull m t :=
  ⟨2, by rw [siFull_eq_two_mul hm]; ring⟩

/-- Reduction from the parent modulus to the child modulus. -/
def siReduce (hm : t ≤ m) : ZMod (siFull m t) →+* ZMod (siHalf m t) :=
  ZMod.castHom (siHalf_dvd hm) _

/-- The sheet: the nonzero element killed by the reduction. -/
def siSheet (m t : ℕ) : ZMod (siFull m t) := ((siHalf m t : ℕ) : ZMod (siFull m t))

/-- The sheet is its own negative. -/
lemma siSheet_add_self (hm : t ≤ m) :
    siSheet m t + siSheet m t = 0 := by
  unfold siSheet
  rw [← Nat.cast_add,
    show siHalf m t + siHalf m t = siFull m t from by
      have := siFull_eq_two_mul (m := m) (t := t) hm; omega]
  exact ZMod.natCast_self _

/-- The sheet is killed by the reduction. -/
lemma siReduce_sheet (hm : t ≤ m) : siReduce hm (siSheet m t) = 0 := by
  unfold siReduce siSheet
  rw [map_natCast]
  exact ZMod.natCast_self _

/-- **The kernel of the reduction is exactly `{0, sheet}`**, so a child
entry has exactly two lifts, differing by the sheet. -/
lemma siReduce_kernel (hm : t ≤ m) (x : ZMod (siFull m t))
    (hx : siReduce hm x = 0) : x = 0 ∨ x = siSheet m t := by
  haveI : NeZero (siFull m t) := ⟨by have := siFull_pos hm; omega⟩
  haveI : NeZero (siHalf m t) := ⟨by have := siHalf_pos hm; omega⟩
  have hval : ((x.val : ℕ) : ZMod (siFull m t)) = x :=
    ZMod.natCast_rightInverse x
  have hred : siReduce hm ((x.val : ℕ) : ZMod (siFull m t))
      = ((x.val : ℕ) : ZMod (siHalf m t)) := map_natCast _ _
  rw [hval, hx] at hred
  have hdvd : siHalf m t ∣ x.val :=
    (ZMod.natCast_eq_zero_iff _ _).mp hred.symm
  obtain ⟨c, hc⟩ := hdvd
  have hlt : x.val < siFull m t := ZMod.val_lt x
  have hmod := siFull_eq_two_mul (m := m) (t := t) hm
  have hhp := siHalf_pos (m := m) (t := t) hm
  have hc2 : c < 2 := by
    by_contra hcon
    have h2 : siHalf m t * 2 ≤ siHalf m t * c :=
      Nat.mul_le_mul_left _ (Nat.not_lt.mp hcon)
    omega
  interval_cases c
  · left; rw [← hval, hc]; simp
  · right; rw [← hval, hc, mul_one]; rfl

/-- The two lifts of a child entry. -/
lemma siReduce_eq_iff (hm : t ≤ m) (x y : ZMod (siFull m t)) :
    siReduce hm x = siReduce hm y ↔ (x = y ∨ x = y + siSheet m t) := by
  constructor
  · intro h
    have h0 : siReduce hm (x - y) = 0 := by rw [map_sub, h, sub_self]
    rcases siReduce_kernel hm _ h0 with h1 | h1
    · left; have := sub_eq_zero.mp h1; exact this
    · right; have : x = y + (x - y) := by ring
      rw [this, h1]
  · rintro (rfl | rfl)
    · rfl
    · rw [map_add, siReduce_sheet hm, add_zero]

/-! ### Sheet bits -/

/-- **Lifts are indexed by a bit.**  If two parent entries have the same
reduction, they differ by a multiple of the sheet with coefficient `0` or
`1` — the sheet BIT. -/
lemma exists_sheet_bit (hm : t ≤ m) (x y : ZMod (siFull m t))
    (h : siReduce hm x = siReduce hm y) :
    ∃ b : ℕ, b < 2 ∧ x = y + b • siSheet m t := by
  rcases (siReduce_eq_iff hm x y).mp h with h1 | h1
  · exact ⟨0, by norm_num, by simpa using h1⟩
  · exact ⟨1, by norm_num, by simpa using h1⟩

/-- **Only the parity of a sheet coefficient matters.**  This is what turns
the group equation for a rival into a statement about `sheetSum`, which
counts sheet bits modulo two. -/
lemma nsmul_siSheet (hm : t ≤ m) (c : ℕ) :
    c • siSheet m t = (c % 2) • siSheet m t := by
  conv_lhs => rw [← Nat.div_add_mod c 2]
  rw [add_smul]
  have h2 : (2 * (c / 2)) • siSheet m t = 0 := by
    rw [mul_comm, mul_smul, two_smul, siSheet_add_self hm, smul_zero]
  rw [h2, zero_add]

/-- Two sheet coefficients of equal parity give the same contribution. -/
lemma nsmul_siSheet_congr (hm : t ≤ m) {c c' : ℕ} (h : c % 2 = c' % 2) :
    c • siSheet m t = c' • siSheet m t := by
  rw [nsmul_siSheet hm c, nsmul_siSheet hm c', h]

end Sheet

end MinModulus
