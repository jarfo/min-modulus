import MinModulus.G2AnchoredUnion

/-! Counterexamples to uniform pairwise-quarter and triple-eighth bounds
for the project's anchored cubes. The odd anchored-union conjecture is
consistent with this example: its union is all of ZMod 15. -/
namespace MinModulus.Research
open Finset

def anchoredIntersectionControl : Fin 4 → ZMod 15 := ![0,11,8,6]

private theorem anchoredIntersectionControl_bounded :
    ∀ k : Fin 4 → Fin 5, (∑ i, (k i).val)=4 →
      (∑ i, (k i).val • anchoredIntersectionControl i)=
        (∑ i, anchoredIntersectionControl i) →
      ∀ i, (k i).val=1 := by
  decide +kernel

theorem anchoredIntersectionControl_valid : ValidTuple anchoredIntersectionControl := by
  intro k hcount hsum
  have hb (i : Fin 4) : k i < 5 := by
    have h := Finset.single_le_sum (fun j _ ↦ Nat.zero_le (k j)) (Finset.mem_univ i)
    rw [hcount] at h
    omega
  exact anchoredIntersectionControl_bounded (fun i ↦ ⟨k i,hb i⟩) hcount hsum

theorem anchoredIntersectionControl_cube_cards :
    ∀ i : Fin 4, (anchoredCube anchoredIntersectionControl i).card=8 := by
  decide +kernel

theorem anchoredIntersectionControl_pair :
    anchoredCube anchoredIntersectionControl 0 ∩ anchoredCube anchoredIntersectionControl 1 =
      ({0,4,10,11,14} : Finset (ZMod 15)) := by
  decide +kernel

theorem anchoredIntersectionControl_triple :
    anchoredCube anchoredIntersectionControl 0 ∩ anchoredCube anchoredIntersectionControl 1 ∩
      anchoredCube anchoredIntersectionControl 3 = ({0,11,14} : Finset (ZMod 15)) := by
  decide +kernel

theorem anchoredIntersectionControl_pair_card :
    (anchoredCube anchoredIntersectionControl 0 ∩ anchoredCube anchoredIntersectionControl 1).card=5 := by
  rw [anchoredIntersectionControl_pair]
  decide

theorem anchoredIntersectionControl_triple_card :
    (anchoredCube anchoredIntersectionControl 0 ∩ anchoredCube anchoredIntersectionControl 1 ∩
      anchoredCube anchoredIntersectionControl 3).card=3 := by
  rw [anchoredIntersectionControl_triple]
  decide

theorem anchoredIntersectionControl_union : anchoredUnion anchoredIntersectionControl=Finset.univ := by
  decide +kernel

theorem anchored_pair_quarter_counterexample :
    ∃ g : Fin 4 → ZMod 15, ValidTuple g ∧
      2^(4-2) < (anchoredCube g 0 ∩ anchoredCube g 1).card := by
  exact ⟨anchoredIntersectionControl, anchoredIntersectionControl_valid,
    by rw [anchoredIntersectionControl_pair_card]; decide⟩

theorem anchored_triple_eighth_counterexample :
    ∃ g : Fin 4 → ZMod 15, ValidTuple g ∧
      2^(4-3) < (anchoredCube g 0 ∩ anchoredCube g 1 ∩ anchoredCube g 3).card := by
  exact ⟨anchoredIntersectionControl, anchoredIntersectionControl_valid,
    by rw [anchoredIntersectionControl_triple_card]; decide⟩

end MinModulus.Research
