/-
# Kernel-checked small bases for the full-quotient-prefix induction
-/
import MinModulus.SILiftOddComplete

namespace MinModulus
open Finset

/-- A bounded, explicitly checked multiplicity rival contradicts validity. -/
theorem not_validTuple_of_bounded_multiplicity_rival
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (h : ∃ k : Fin n → Fin (n + 1),
      (∑ i, (k i).val) = n ∧ (∑ i, (k i).val • g i) = ∑ i, g i ∧
      ∃ i, (k i).val ≠ 1) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨k, hsum, hval, i, hi⟩ := h
  exact hi (hg (fun i ↦ (k i).val) hsum hval i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every three-tuple modulo four has an explicit double/pair equality. -/
theorem not_validTuple_three_mod_four (g : Fin 3 → ZMod 4) : ¬ ValidTuple g := by
  have h : ∀ g : Fin 3 → ZMod 4, ∃ a b c : Fin 3, a ≠ b ∧ 2 • g c = g a + g b := by decide
  obtain ⟨a, b, c, hab, heq⟩ := h g
  exact not_validTuple_of_double_eq_distinct_pair g a b c hab heq

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact dimension-four base at modulus eight. Only this fixed small
base is enumerated; the higher-dimensional induction is uniform. -/
theorem bounded_rival_four_mod_eight_of_si_prefix (c d x : ZMod 8)
    (hc : ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) c = 1)
    (hd : ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) d = 3) :
    ∃ k : Fin 4 → Fin 5,
      (∑ i, (k i).val) = 4 ∧
      (∑ i, (k i).val • (![0, c, d, x] : Fin 4 → ZMod 8) i) = ∑ i, (![0, c, d, x] : Fin 4 → ZMod 8) i ∧
      ∃ i, (k i).val ≠ 1 := by
  have h : ∀ c d x : ZMod 8,
      ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) c = 1 →
      ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) d = 3 →
      ∃ k : Fin 4 → Fin 5,
        (∑ i, (k i).val) = 4 ∧
        (∑ i, (k i).val • (![0, c, d, x] : Fin 4 → ZMod 8) i) = ∑ i, (![0, c, d, x] : Fin 4 → ZMod 8) i ∧
        ∃ i, (k i).val ≠ 1 := by decide
  exact h c d x hc hd

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Exact dimension-four base at modulus ten. This is a bounded kernel
computation producing rivals, not an external certificate or an open gate. -/
theorem bounded_rival_four_mod_ten_of_si_prefix (c d x : ZMod 10)
    (hc : ZMod.castHom (by decide : 5 ∣ 10) (ZMod 5) c = 1)
    (hd : ZMod.castHom (by decide : 5 ∣ 10) (ZMod 5) d = 3) :
    ∃ k : Fin 4 → Fin 5,
      (∑ i, (k i).val) = 4 ∧
      (∑ i, (k i).val • (![0, c, d, x] : Fin 4 → ZMod 10) i) = ∑ i, (![0, c, d, x] : Fin 4 → ZMod 10) i ∧
      ∃ i, (k i).val ≠ 1 := by
  have h : ∀ c d x : ZMod 10,
      ZMod.castHom (by decide : 5 ∣ 10) (ZMod 5) c = 1 →
      ZMod.castHom (by decide : 5 ∣ 10) (ZMod 5) d = 3 →
      ∃ k : Fin 4 → Fin 5,
        (∑ i, (k i).val) = 4 ∧
        (∑ i, (k i).val • (![0, c, d, x] : Fin 4 → ZMod 10) i) = ∑ i, (![0, c, d, x] : Fin 4 → ZMod 10) i ∧
        ∃ i, (k i).val ≠ 1 := by decide
  exact h c d x hc hd

/-- Actual zero normalization connects the modulus-eight base certificate
to a full independently lifted SI quotient prefix. -/
theorem not_validTuple_four_mod_eight_of_si_quotient_prefix
    (g : Fin 4 → ZMod 8)
    (hprefix : ∀ i : Fin 3, ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4)
      (g i.castSucc) = (a i.val : ZMod 4)) : ¬ ValidTuple g := by
  intro hg
  let v := fun i ↦ g i - g 0
  have hv : ValidTuple v := validTuple_sub_const g hg (g 0)
  have hz : ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) (g 0) = 0 := by
    simpa [a] using hprefix 0
  have hc : ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) (v 1) = 1 := by
    change ZMod.castHom _ _ (g 1 - g 0) = 1
    rw [map_sub, hz, sub_zero]
    simpa [a] using hprefix 1
  have hd : ZMod.castHom (by decide : 4 ∣ 8) (ZMod 4) (v 2) = 3 := by
    change ZMod.castHom _ _ (g 2 - g 0) = 3
    rw [map_sub, hz, sub_zero]
    simpa [a] using hprefix 2
  have hgf : v = ![0, v 1, v 2, v 3] := by
    funext i
    fin_cases i <;> simp [v]
  apply not_validTuple_of_bounded_multiplicity_rival v _ hv
  rw [hgf]
  exact bounded_rival_four_mod_eight_of_si_prefix _ _ _ hc hd

/-- Actual zero normalization connects the modulus-ten base certificate
to a full independently lifted SI quotient prefix. -/
theorem not_validTuple_four_mod_ten_of_si_quotient_prefix
    (g : Fin 4 → ZMod 10)
    (hprefix : ∀ i : Fin 3, ZMod.castHom (by decide : 5 ∣ 10) (ZMod 5)
      (g i.castSucc) = (a i.val : ZMod 5)) : ¬ ValidTuple g := by
  intro hg
  let v := fun i ↦ g i - g 0
  have hv : ValidTuple v := validTuple_sub_const g hg (g 0)
  have hz : ZMod.castHom (by decide : 5 ∣ 10) (ZMod 5) (g 0) = 0 := by
    simpa [a] using hprefix 0
  have hc : ZMod.castHom (by decide : 5 ∣ 10) (ZMod 5) (v 1) = 1 := by
    change ZMod.castHom _ _ (g 1 - g 0) = 1
    rw [map_sub, hz, sub_zero]
    simpa [a] using hprefix 1
  have hd : ZMod.castHom (by decide : 5 ∣ 10) (ZMod 5) (v 2) = 3 := by
    change ZMod.castHom _ _ (g 2 - g 0) = 3
    rw [map_sub, hz, sub_zero]
    simpa [a] using hprefix 2
  have hgf : v = ![0, v 1, v 2, v 3] := by
    funext i
    fin_cases i <;> simp [v]
  apply not_validTuple_of_bounded_multiplicity_rival v _ hv
  rw [hgf]
  exact bounded_rival_four_mod_ten_of_si_prefix _ _ _ hc hd

/-- Three-entry even subbinary validity already gives the fixed endpoint. -/
theorem valid_fixed_three_of_valid_subbinary_even_tuple
    {M : ℕ} [NeZero M] (g : Fin 3 → ZMod (2 * M)) (hg : ValidTuple g)
    (hupper : 2 * M < 8) : Valid 3 (2 * M) := by
  have hb := two_pow_pred_le_card_of_validTuple g hg
  norm_num only [Nat.reduceSub, Nat.reducePow, ZMod.card] at hb
  have hM : M = 2 ∨ M = 3 := by omega
  rcases hM with rfl | rfl
  · exact False.elim (not_validTuple_three_mod_four g hg)
  · exact valid_gap (n := 3) (t := 1) (by decide) (by decide)

/-- Four-entry full SI quotient prefixes give a fixed valid modulus
throughout the subbinary range. Only moduli eight and ten need the exact
base certificates; twelve and fourteen are proved fixed power gaps. -/
theorem valid_fixed_four_of_valid_subbinary_si_lift_prefix
    {M : ℕ} [NeZero M] (g : Fin 4 → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin 3, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hupper : 2 * M < 16) : Valid 4 (2 * M) := by
  have hb := two_pow_pred_le_card_of_validTuple g hg
  norm_num only [Nat.reduceSub, Nat.reducePow, ZMod.card] at hb
  have hM : M = 4 ∨ M = 5 ∨ M = 6 ∨ M = 7 := by omega
  rcases hM with rfl | rfl | rfl | rfl
  · exact False.elim (not_validTuple_four_mod_eight_of_si_quotient_prefix g hprefix hg)
  · exact False.elim (not_validTuple_four_mod_ten_of_si_quotient_prefix g hprefix hg)
  · exact valid_gap (n := 4) (t := 2) (by decide) (by decide)
  · exact valid_gap (n := 4) (t := 1) (by decide) (by decide)

end MinModulus
