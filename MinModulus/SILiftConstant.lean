import MinModulus.SILiftReduce
import MinModulus.G1OddPrimarySingletonComplement

/-!
# The SI-lift with constant sheet bits

A child lifted by the SAME sheet bit on every coordinate is a translate of
the unlifted child, so `si_extra_eq_top_of_valid` applies after shifting.
This settles the constant-bit column of the eight valid configurations.
-/

namespace MinModulus

open Finset

/-- The SI parent with a constant shift `c` on the child coordinates. -/
def siParentShift (m : ℕ) {N : ℕ} (c : ZMod N) (e : ZMod N) :
    Fin (m + 1) → ZMod N :=
  Fin.snoc (fun i : Fin m => ((2 ^ i.val - 1 : ℕ) : ZMod N) + c) e

@[simp] lemma siParentShift_castSucc (m : ℕ) {N : ℕ} (c e : ZMod N)
    (i : Fin m) :
    siParentShift m c e (Fin.castSucc i) = ((2 ^ i.val - 1 : ℕ) : ZMod N) + c := by
  rw [siParentShift, Fin.snoc_castSucc]

@[simp] lemma siParentShift_last (m : ℕ) {N : ℕ} (c e : ZMod N) :
    siParentShift m c e (Fin.last m) = e := by
  rw [siParentShift, Fin.snoc_last]

/-- Shifting the whole tuple turns a constant-bit lift into the unlifted
child, with the extra shifted the same way. -/
lemma siParentShift_sub (m : ℕ) {N : ℕ} (c e : ZMod N) (i : Fin (m + 1)) :
    siParentShift m c e i - c
      = ((siParent m 0 i : ℕ) : ZMod N)
        + (if i = Fin.last m then e - c else 0) := by
  induction i using Fin.lastCases with
  | last =>
    rw [siParentShift_last, if_pos rfl]
    simp [siParent]
  | cast j =>
    rw [siParentShift_castSucc, if_neg (by
      intro h; exact absurd h (Fin.castSucc_ne_last j)), add_zero]
    rw [siParent_castSucc]
    ring

/-- **Constant sheet bits force the extra.**  If the super-increasing
child shifted by a constant `c` together with an extra `e` is valid at the
stratum modulus, then `e - c` is the top super-increasing coordinate. -/
theorem si_extra_eq_top_of_valid_shift {m s : ℕ} (hm : 4 ≤ m) (hs : 2 ≤ s)
    (hsn : 2 ^ s ≤ m + 1)
    (c e : ZMod (2 ^ (m + 1) - 2 ^ s))
    (hv : ValidTuple (siParentShift m c e)) :
    e - c = ((2 ^ m - 1 : ℕ) : ZMod (2 ^ (m + 1) - 2 ^ s)) := by
  have hpow : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
  have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have h2s : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_pow _ _ (by norm_num)
  have hmlt : m < 2 ^ m := Nat.lt_two_pow_self
  have hsm : (2 : ℕ) ^ s ≤ 2 ^ m := by
    refine Nat.pow_le_pow_right (by norm_num) ?_
    by_contra hc
    have h2 : (2 : ℕ) ^ (m + 1) ≤ 2 ^ s :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  haveI : NeZero (2 ^ (m + 1) - 2 ^ s) := ⟨by omega⟩
  -- translate by `-c`
  have hsub := validTuple_sub_const _ hv c
  -- the translated tuple is the unlifted child with extra `e - c`
  set e' : ℕ := (e - c).val with he'
  have hval : ∀ i, siParentShift m c e i - c
      = ((siParent m e' i : ℕ) : ZMod (2 ^ (m + 1) - 2 ^ s)) := by
    intro i
    rw [siParentShift_sub]
    induction i using Fin.lastCases with
    | last =>
      rw [if_pos rfl, siParent_last]
      simp only [siParent, Fin.snoc_last, Nat.cast_zero, zero_add]
      rw [he', ZMod.natCast_rightInverse (e - c)]
    | cast j =>
      rw [if_neg (by intro h; exact absurd h (Fin.castSucc_ne_last j)),
        add_zero, siParent_castSucc, siParent_castSucc]
  rw [funext hval] at hsub
  have := si_extra_eq_top_of_valid (m := m) (s := s) (e := e') hm hs hsn
    (by rw [he']; exact ZMod.val_lt _) hsub
  rw [← this, he', ZMod.natCast_rightInverse (e - c)]

end MinModulus
