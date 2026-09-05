/-
# Exact criticality and a regression against overlap-only reasoning

For a valid tuple of length `n`, write `O` for the overlap of its anchored
subset-sum cube with a translate and `U` for the residues outside their
union. The exact identity is `N + O = 2^n + U`. Thus the critical range is
`U + gap < O`, not merely `gap < O`.

The existing valid seven-tuple modulo 1006 has a three-omission half-witness
and no common touched coordinate, despite overlap exceeding the first-even
gap at every anchor. This refutes the weaker overlap-only shortcut, not
critical G1: its uncovered mass is large and its modulus is noncritical.
-/
import MinModulus.G1Counterexample
import MinModulus.G1CriticalThreeOmissions

namespace MinModulus

open Finset

/-- Inclusion-exclusion without discarding the ambient complement. -/
theorem card_subsetSumShift_uncovered_add_two_pow
    {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (g : Fin (m + 1) → G) (hg : ValidTuple g) (h : G) :
    (Finset.univ \ (subsetSumRange g ∪ subsetSumShiftRange g h)).card +
      2 ^ (m + 1) = Fintype.card G +
        (subsetSumRange g ∩ subsetSumShiftRange g h).card := by
  have hu := Finset.card_union_add_card_inter
    (subsetSumRange g) (subsetSumShiftRange g h)
  rw [card_subsetSumRange g hg, card_subsetSumShiftRange g hg h] at hu
  have hc := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ
    (subsetSumRange g ∪ subsetSumShiftRange g h))
  rw [Finset.card_univ] at hc
  rw [pow_succ]
  omega

/-- The quantitative modulus hypothesis is exactly an overlap surplus over
both the prescribed gap and the uncovered residues. -/
theorem modulus_add_gap_lt_iff_uncovered_add_gap_lt_overlap
    {m N K : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g) (h : ZMod N) :
    N + K < 2 ^ (m + 1) ↔
      (Finset.univ \ (subsetSumRange g ∪ subsetSumShiftRange g h)).card + K <
        (subsetSumRange g ∩ subsetSumShiftRange g h).card := by
  have heq := card_subsetSumShift_uncovered_add_two_pow g hg h
  rw [ZMod.card] at heq
  omega

/-- Exact stratum criticality in subset-sum language. Merely keeping the
gap lower bound on overlap loses information. -/
theorem criticalRange_iff_uncovered_add_gap_lt_overlap
    {m N t : ℕ} [NeZero N]
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g) (h : ZMod N) :
    N < stratumBound (m + 1) t ↔
      (Finset.univ \ (subsetSumRange g ∪ subsetSumShiftRange g h)).card +
        2 ^ min t (Nat.log 2 (m + 1)) <
          (subsetSumRange g ∩ subsetSumShiftRange g h).card := by
  rw [stratumBound, Nat.lt_sub_iff_add_lt]
  exact modulus_add_gap_lt_iff_uncovered_add_gap_lt_overlap g hg h

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- Kernel-computed overlap counts at all seven choices of anchor in the
existing unrestricted-G1 counterexample. -/
theorem g1Counterexample_all_anchor_overlap
    (r : Fin 7) :
    let g := fun i ↦ g1CounterexampleTuple (Equiv.swap (0 : Fin 7) r i)
    (subsetSumRange g ∩ subsetSumShiftRange g (503 : ZMod 1006)).card =
      (![16, 16, 16, 40, 40, 16, 24] : Fin 7 → ℕ) r := by
  fin_cases r <;> decide

/-- The original anchor leaves 894 residues outside both cubes, explaining
why its overlap of 16 does not certify criticality. -/
theorem g1Counterexample_uncovered :
    (Finset.univ \ (subsetSumRange g1CounterexampleTuple ∪
      subsetSumShiftRange g1CounterexampleTuple (503 : ZMod 1006))).card = 894 := by
  have heq := card_subsetSumShift_uncovered_add_two_pow
    g1CounterexampleTuple g1CounterexampleTuple_valid (503 : ZMod 1006)
  have hover : (subsetSumRange g1CounterexampleTuple ∩
      subsetSumShiftRange g1CounterexampleTuple (503 : ZMod 1006)).card = 16 := by
    simpa using g1Counterexample_all_anchor_overlap 0
  rw [ZMod.card, hover] at heq
  norm_num at heq
  omega

/-- Three omissions and overlap greater than the first-stratum gap at every
anchor do not force common touch without the actual critical modulus bound. -/
theorem g1Counterexample_large_overlap_without_common_touch :
    ∃ g : Fin 7 → ZMod 1006,
      ValidTuple g ∧ WitnessThreeDistinctOmissions g (503 : ZMod 1006) ∧
      (∀ r : Fin 7,
        let gr := fun i ↦ g (Equiv.swap (0 : Fin 7) r i)
        2 < (subsetSumRange gr ∩ subsetSumShiftRange gr (503 : ZMod 1006)).card) ∧
      ¬∃ j : Fin 7, ∀ c : Fin 7 → ℤ, Witness g (503 : ZMod 1006) c → c j ≠ 0 := by
  refine ⟨g1CounterexampleTuple, g1CounterexampleTuple_valid, ?_, ?_,
    g1Counterexample_no_common_touched⟩
  · refine ⟨g1CounterexampleWitnessE, 0, 2, 5,
      g1CounterexampleWitnessE_isWitness, by decide, by decide, by decide,
      by decide, by decide, by decide⟩
  · intro r
    dsimp only
    rw [g1Counterexample_all_anchor_overlap]
    fin_cases r <;> decide

end MinModulus
