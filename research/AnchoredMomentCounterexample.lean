import research.AnchoredIntersectionCounterexample

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Sum of the intersection sizes over all r-element sets of anchors. -/
def anchoredIntersectionMoment {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (r : ℕ) : ℕ :=
  ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard r,
    ((Finset.univ : Finset (ZMod N)).filter
      (fun x ↦ ∀ i ∈ I, x ∈ anchoredCube g i)).card

/-- The already verified odd control also exceeds the summed pairwise-quarter bound. -/
theorem anchoredIntersectionControl_pair_moment :
    anchoredIntersectionMoment anchoredIntersectionControl 2=25 := by
  decide +kernel

/-- Summing over triples does not repair the uniform eighth bound either. -/
theorem anchoredIntersectionControl_triple_moment :
    anchoredIntersectionMoment anchoredIntersectionControl 3=9 := by
  decide +kernel

/-- No two cubes of this valid control meet only at zero. The relation-free
pair criterion is therefore not necessary for the sharp odd bound. -/
theorem anchoredIntersectionControl_all_pairs_nontrivial :
    ∀ i j : Fin 4, i ≠ j →
      1 < (anchoredCube anchoredIntersectionControl i ∩
        anchoredCube anchoredIntersectionControl j).card := by
  decide +kernel

/-- A single valid tuple refutes both averaged moment bounds and universal
existence of a relation-free pair, while its anchored union is still sharp. -/
theorem anchored_moment_and_relation_free_counterexample :
    ∃ g : Fin 4 → ZMod 15, ValidTuple g ∧
      (4 : ℕ).choose 2*2^(4-2) < anchoredIntersectionMoment g 2 ∧
      (4 : ℕ).choose 3*2^(4-3) < anchoredIntersectionMoment g 3 ∧
      (∀ i j : Fin 4, i ≠ j → 1 < (anchoredCube g i ∩ anchoredCube g j).card) ∧
      anchoredUnion g=Finset.univ := by
  refine ⟨anchoredIntersectionControl,anchoredIntersectionControl_valid,?_,?_,
    anchoredIntersectionControl_all_pairs_nontrivial,anchoredIntersectionControl_union⟩
  · rw [anchoredIntersectionControl_pair_moment]
    decide
  · rw [anchoredIntersectionControl_triple_moment]
    decide

end MinModulus.Research
