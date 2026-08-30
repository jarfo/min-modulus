/-
# Kernel-checked normalized four-coordinate SHC exclusions

This file discharges the normalized finite-search half of the first open SHC
window.  Coordinate sorting reduces a tuple with first coordinate `1` to an
increasing tuple of canonical `ZMod` representatives.  For each odd order from
17 through 29, a small executable checker then verifies that dissociation and
the head-2 shell clause are already incompatible.

The checks use `decide`, not `native_decide`, so their proof terms are reduced
by the Lean kernel and introduce no native-code evaluation axiom.
-/
import MinModulus.SHCBaseCases
import Mathlib.Data.Fin.Tuple.Sort

namespace MinModulus

open Finset

/-- No coordinate of an SHC family is zero. -/
theorem SHC.ne_zero {m : ℕ} {G : Type*} [AddCommGroup G]
    (h : Fin m → G) (hs : SHC h) (i : Fin m) : h i ≠ 0 := by
  intro hi
  have heq : (∑ j ∈ ({i} : Finset (Fin m)), h j) =
      ∑ j ∈ (∅ : Finset (Fin m)), h j := by
    simp [hi]
  exact Finset.singleton_ne_empty i (hs.dis heq)

/-- Sorted form of the normalized four-coordinate exclusion. -/
def SortedNormalizedSHCFourExcluded (N : ℕ) : Prop :=
  ∀ h : Fin 4 → ZMod N, h 0 = 1 → Monotone (fun i => (h i).val) → ¬ SHC h

/-- Sorting canonical representatives preserves the first coordinate `1`, so
a sorted normalized exclusion implies the unrestricted normalized one. -/
theorem normalizedSHCFourExcluded_of_sorted {N : ℕ} (hN : 2 ≤ N)
    (hsorted : SortedNormalizedSHCFourExcluded N) : NormalizedSHCFourExcluded N := by
  letI : NeZero N := ⟨by omega⟩
  letI : Fact (1 < N) := ⟨hN⟩
  intro h h0 hs
  let p : Fin 4 ≃ Fin 4 := Tuple.sort (fun i => (h i).val)
  let h' : Fin 4 → ZMod N := h ∘ p
  have hsh' : SHC h' := hs.reindex_equiv h p
  have hmono : Monotone (fun i => (h' i).val) := by
    exact Tuple.monotone_sort (fun i => (h i).val)
  have h'0 : h' 0 = 1 := by
    let j : Fin 4 := p.symm 0
    have hj : h' j = 1 := by
      simp [h', j, p, h0]
    have hle : (h' 0).val ≤ 1 := by
      have := hmono (Fin.zero_le j)
      simpa [hj, ZMod.val_one] using this
    have hpos : 0 < (h' 0).val := ZMod.val_pos.mpr (hsh'.ne_zero h' 0)
    apply ZMod.val_injective
    simpa [ZMod.val_one] using (show (h' 0).val = 1 by omega)
  exact hsorted h' h'0 hmono hsh'

/-- Executable dissociation and head-2 shell checker for four coordinates. -/
private def checkSHC4 {N : ℕ} [NeZero N] (h : Fin 4 → ZMod N) : Bool :=
  decide (∀ S T : Finset (Fin 4), (∑ j ∈ S, h j) = ∑ j ∈ T, h j → S = T) &&
  decide (∀ (x : Fin 4) (P M : Finset (Fin 4)), x ∉ P → x ∉ M → Disjoint P M →
    P.card + 1 ≤ M.card → 2 • h x + ∑ j ∈ P, h j ≠ ∑ j ∈ M, h j)

/-- Reconstruct a normalized four-tuple from its final three coordinates. -/
private def normalizedFour {N : ℕ} (t : Fin 3 → ZMod N) : Fin 4 → ZMod N :=
  Fin.cons 1 t

private theorem checkSHC4_eq_true_of_shc {N : ℕ} [NeZero N]
    (h : Fin 4 → ZMod N) (hs : SHC h) : checkSHC4 h = true := by
  simp only [checkSHC4, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨hs.dis, hs.sh2⟩

private theorem sorted_excluded_of_no_check {N : ℕ} [NeZero N]
    (hno : ¬ ∃ t : Fin 3 → ZMod N,
      Monotone (fun i => (normalizedFour t i).val) ∧ checkSHC4 (normalizedFour t) = true) :
    SortedNormalizedSHCFourExcluded N := by
  intro h h0 hmono hs
  let t : Fin 3 → ZMod N := Fin.tail h
  apply hno
  refine ⟨t, ?_, ?_⟩
  · simpa [normalizedFour, t, ← h0, Fin.cons_self_tail] using hmono
  · simpa [normalizedFour, t, ← h0, Fin.cons_self_tail] using checkSHC4_eq_true_of_shc h hs

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem no_sorted_check_seventeen : ¬ ∃ t : Fin 3 → ZMod 17,
    Monotone (fun i => (normalizedFour t i).val) ∧
      checkSHC4 (normalizedFour t) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem no_sorted_check_nineteen : ¬ ∃ t : Fin 3 → ZMod 19,
    Monotone (fun i => (normalizedFour t i).val) ∧
      checkSHC4 (normalizedFour t) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem no_sorted_check_twenty_one : ¬ ∃ t : Fin 3 → ZMod 21,
    Monotone (fun i => (normalizedFour t i).val) ∧
      checkSHC4 (normalizedFour t) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem no_sorted_check_twenty_three : ¬ ∃ t : Fin 3 → ZMod 23,
    Monotone (fun i => (normalizedFour t i).val) ∧
      checkSHC4 (normalizedFour t) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem no_sorted_check_twenty_five : ¬ ∃ t : Fin 3 → ZMod 25,
    Monotone (fun i => (normalizedFour t i).val) ∧
      checkSHC4 (normalizedFour t) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem no_sorted_check_twenty_seven : ¬ ∃ t : Fin 3 → ZMod 27,
    Monotone (fun i => (normalizedFour t i).val) ∧
      checkSHC4 (normalizedFour t) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 50000000 in
private theorem no_sorted_check_twenty_nine : ¬ ∃ t : Fin 3 → ZMod 29,
    Monotone (fun i => (normalizedFour t i).val) ∧
      checkSHC4 (normalizedFour t) = true := by
  decide

theorem normalized_shc_four_excluded_seventeen : NormalizedSHCFourExcluded 17 :=
  normalizedSHCFourExcluded_of_sorted (by omega)
    (sorted_excluded_of_no_check no_sorted_check_seventeen)

theorem normalized_shc_four_excluded_nineteen : NormalizedSHCFourExcluded 19 :=
  normalizedSHCFourExcluded_of_sorted (by omega)
    (sorted_excluded_of_no_check no_sorted_check_nineteen)

theorem normalized_shc_four_excluded_twenty_one : NormalizedSHCFourExcluded 21 :=
  normalizedSHCFourExcluded_of_sorted (by omega)
    (sorted_excluded_of_no_check no_sorted_check_twenty_one)

theorem normalized_shc_four_excluded_twenty_three : NormalizedSHCFourExcluded 23 :=
  normalizedSHCFourExcluded_of_sorted (by omega)
    (sorted_excluded_of_no_check no_sorted_check_twenty_three)

theorem normalized_shc_four_excluded_twenty_five : NormalizedSHCFourExcluded 25 :=
  normalizedSHCFourExcluded_of_sorted (by omega)
    (sorted_excluded_of_no_check no_sorted_check_twenty_five)

theorem normalized_shc_four_excluded_twenty_seven : NormalizedSHCFourExcluded 27 :=
  normalizedSHCFourExcluded_of_sorted (by omega)
    (sorted_excluded_of_no_check no_sorted_check_twenty_seven)

theorem normalized_shc_four_excluded_twenty_nine : NormalizedSHCFourExcluded 29 :=
  normalizedSHCFourExcluded_of_sorted (by omega)
    (sorted_excluded_of_no_check no_sorted_check_twenty_nine)

/-- Every odd modulus in the first four-coordinate strict window satisfies the
normalized SHC exclusion. -/
theorem normalized_shc_four_excluded_of_odd_window {N : ℕ} (hodd : Odd N)
    (hlower : 17 ≤ N) (hupper : N ≤ 29) : NormalizedSHCFourExcluded N := by
  obtain ⟨k, hk⟩ := hodd
  have hcases : N = 17 ∨ N = 19 ∨ N = 21 ∨ N = 23 ∨ N = 25 ∨ N = 27 ∨ N = 29 := by
    omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact normalized_shc_four_excluded_seventeen
  · exact normalized_shc_four_excluded_nineteen
  · exact normalized_shc_four_excluded_twenty_one
  · exact normalized_shc_four_excluded_twenty_three
  · exact normalized_shc_four_excluded_twenty_five
  · exact normalized_shc_four_excluded_twenty_seven
  · exact normalized_shc_four_excluded_twenty_nine

end MinModulus
