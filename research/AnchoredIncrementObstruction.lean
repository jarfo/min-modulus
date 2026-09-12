import MinModulus.G2AnchoredUnion
import MinModulus.UniqueSums

/-! Even a choice of anchor order cannot ensure separate geometric-series
increments. The canonical valid seven-tuple gives the obstruction already
at the third anchor. Its cumulative union bound nevertheless holds. -/
namespace MinModulus.Research
open Finset

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def anchoredSevenControl : Fin 7 → ZMod 127 := ![0,1,3,7,15,31,63]

private theorem fixed_validity_transport {n N : ℕ} (hv : Valid n N) :
    ValidTuple (fun i : Fin n ↦ (a i.val : ZMod N)) := by
  intro k hksum hkval
  let K : ℕ → ℕ := fun i ↦ if hi : i < n then k ⟨i, hi⟩ else 0
  have hKsum : dsum n K = n := by
    unfold dsum
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [K] using hksum
  have hcast :
      ((∑ i : Fin n, k i * a i.val : ℕ) : ZMod N)
        = ((∑ i : Fin n, a i.val : ℕ) : ZMod N) := by
    push_cast
    simpa [nsmul_eq_mul] using hkval
  have hleft : (∑ i ∈ range n, K i * a i) = ∑ i : Fin n, k i * a i.val := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    simp [K]
  have hright : (∑ i ∈ range n, a i) = ∑ i : Fin n, a i.val := by
    rw [← Fin.sum_univ_eq_sum_range]
  have hmod : (∑ i ∈ range n, K i * a i) ≡ (∑ i ∈ range n, a i) [MOD N] := by
    rw [hleft, hright, ← ZMod.natCast_eq_natCast_iff]
    exact hcast
  have hones := hv K hKsum hmod
  intro i
  simpa [K, i.isLt] using hones i.val i.isLt

theorem anchoredSevenControl_valid : ValidTuple anchoredSevenControl := by
  have hv : Valid 7 127 := by
    simpa using (valid_gap (n := 7) (t := 0) (by decide) (by decide))
  have he : anchoredSevenControl = fun i : Fin 7 ↦ (a i.val : ZMod 127) := by
    funext i
    fin_cases i <;> norm_num [anchoredSevenControl, a]
  rw [he]
  exact fixed_validity_transport hv

private def sevenCubeTable : Fin 7 → Finset (ZMod 127) := ![
  {0,1,3,4,7,8,10,11,15,16,18,19,22,23,25,26,31,32,34,35,38,39,41,42,46,47,49,50,53,54,56,57,63,64,66,67,70,71,73,74,78,79,81,82,85,86,88,89,94,95,97,98,101,102,104,105,109,110,112,113,116,117,119,120},
  {0,1,2,5,6,7,8,13,14,15,16,19,20,21,22,29,30,31,32,35,36,37,38,43,44,45,46,49,50,51,52,61,62,63,64,67,68,69,70,75,76,77,78,81,82,83,84,91,92,93,94,97,98,99,100,105,106,107,108,111,112,113,114,126},
  {0,1,2,4,7,9,10,11,12,13,14,16,23,25,26,27,28,29,30,32,35,37,38,39,40,41,42,44,55,57,58,59,60,61,62,64,67,69,70,71,72,73,74,76,83,85,86,87,88,89,90,92,95,97,98,99,100,101,102,104,122,124,125,126},
  {0,1,2,4,7,8,11,13,14,15,17,18,19,20,21,22,24,25,26,28,32,39,43,45,46,47,49,50,51,52,53,54,56,57,58,60,63,64,67,69,70,71,73,74,75,76,77,78,80,81,82,84,88,110,114,116,117,118,120,121,122,123,124,125},
  {0,1,2,4,7,8,11,13,14,15,16,19,21,22,23,25,26,27,28,29,30,33,34,35,36,37,38,40,41,42,44,48,49,50,52,56,64,78,86,90,92,93,94,98,100,101,102,104,105,106,107,108,109,112,113,114,115,116,117,119,120,121,123,126},
  {0,1,2,4,8,14,16,22,26,28,29,30,32,38,42,44,45,46,50,52,53,54,56,57,58,59,60,61,66,68,69,70,72,73,74,75,76,77,80,81,82,83,84,85,87,88,89,91,96,97,98,99,100,101,103,104,105,107,111,112,113,115,119,125},
  {0,2,4,5,8,9,11,13,16,17,19,21,23,25,27,28,32,33,35,37,39,41,43,44,47,49,51,52,55,56,58,60,64,65,67,69,71,73,75,76,79,81,83,84,87,88,90,92,95,97,99,100,103,104,106,108,111,112,114,116,118,120,122,123}
]

private theorem anchoredSevenControl_cubes :
    ∀ i : Fin 7, anchoredCube anchoredSevenControl i = sevenCubeTable i := by
  decide +kernel

theorem anchoredSevenControl_cube_cards :
    ∀ i : Fin 7, (anchoredCube anchoredSevenControl i).card = 64 := by
  simp only [anchoredSevenControl_cubes]
  decide +kernel

theorem anchoredSevenControl_pair_card_range :
    ∀ i j : Fin 7, (anchoredCube anchoredSevenControl i ∪
      anchoredCube anchoredSevenControl j).card ∈ ({64,91,95,100} : Finset ℕ) := by
  simp only [anchoredSevenControl_cubes]
  decide +kernel

theorem anchoredSevenControl_triple_union_le :
    ∀ i j k : Fin 7, (anchoredCube anchoredSevenControl i ∪
      anchoredCube anchoredSevenControl j ∪ anchoredCube anchoredSevenControl k).card ≤ 115 := by
  simp only [anchoredSevenControl_cubes]
  decide +kernel

/-- No first three anchors can contribute at least 64, 32, and 16 new points. -/
theorem anchoredSevenControl_no_first_three_halvings (i j k : Fin 7) :
    ¬ (32 ≤ (anchoredCube anchoredSevenControl j \ anchoredCube anchoredSevenControl i).card ∧
      16 ≤ (anchoredCube anchoredSevenControl k \ (anchoredCube anchoredSevenControl i ∪
        anchoredCube anchoredSevenControl j)).card) := by
  intro ⟨hsecond,hthird⟩
  have hc := anchoredSevenControl_cube_cards i
  have hp := anchoredSevenControl_pair_card_range i j
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  have ht := anchoredSevenControl_triple_union_le i j k
  have hpcount := Finset.card_union (anchoredCube anchoredSevenControl i) (anchoredCube anchoredSevenControl j)
  have htcount := Finset.card_union (anchoredCube anchoredSevenControl i ∪ anchoredCube anchoredSevenControl j) (anchoredCube anchoredSevenControl k)
  have hpdiff := Finset.card_sdiff_add_card_inter (anchoredCube anchoredSevenControl j) (anchoredCube anchoredSevenControl i)
  have htdiff := Finset.card_sdiff_add_card_inter (anchoredCube anchoredSevenControl k) (anchoredCube anchoredSevenControl i ∪ anchoredCube anchoredSevenControl j)
  rw [Finset.inter_comm] at hpdiff htdiff
  omega

theorem anchoredSevenControl_union : anchoredUnion anchoredSevenControl = Finset.univ := by
  unfold anchoredUnion
  rw [show anchoredCube anchoredSevenControl = sevenCubeTable from funext anchoredSevenControl_cubes]
  decide +kernel

/-- Earlier surplus compensates for later increments: cumulative coverage survives. -/
theorem anchoredSevenControl_cumulative_prefix :
    ∀ k : Fin 8, 128 - 2^(7-k.val) ≤
      ((Finset.univ.filter (fun i : Fin 7 ↦ i.val < k.val)).biUnion
        (anchoredCube anchoredSevenControl)).card := by
  rw [show anchoredCube anchoredSevenControl = sevenCubeTable from funext anchoredSevenControl_cubes]
  decide +kernel

theorem anchored_geometric_increment_counterexample :
    ∃ g : Fin 7 → ZMod 127, ValidTuple g ∧ anchoredUnion g = Finset.univ ∧
      ∀ i j k, ¬ (32 ≤ (anchoredCube g j \ anchoredCube g i).card ∧
        16 ≤ (anchoredCube g k \ (anchoredCube g i ∪ anchoredCube g j)).card) := by
  exact ⟨anchoredSevenControl, anchoredSevenControl_valid, anchoredSevenControl_union,
    anchoredSevenControl_no_first_three_halvings⟩

end MinModulus.Research
