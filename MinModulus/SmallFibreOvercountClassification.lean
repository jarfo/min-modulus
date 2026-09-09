import MinModulus.FibreOvercountGap

namespace MinModulus
open Finset
open scoped Classical

/-- Actual shifted values represented by exactly four subsets. -/
noncomputable def tupleFourFibreValues
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) : Finset G :=
  (tupleBinarySumImage g b).filter (fun z ↦
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=4)

/-- Correction at most five cannot contain a five-point fibre,
whose individual excess-pair contribution is at least six. -/
theorem subset_fibre_card_le_four_of_overcount_le_five
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hsmall : tupleBinaryFibreOvercount g b ≤ 5) (z : G) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 4 := by
  have h := fibre_excess_pairs_le_total_overcount g b z
  by_contra hnot
  have hmon := Nat.choose_le_choose 2 (by omega : 4 ≤
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1)
  norm_num [Nat.choose] at hmon
  omega

/-- Under a four-point cap, full correction is the triple-value
count plus three times the four-point-value count. -/
theorem fibre_overcount_eq_triple_add_three_four_count_of_cap_four
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hcap : ∀ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 4) :
    tupleBinaryFibreOvercount g b=(tupleTripleFibreValues g b).card+3*(tupleFourFibreValues g b).card := by
  classical
  have ht : (tupleTripleFibreValues g b).card=
      ∑ z ∈ tupleBinarySumImage g b,
        if (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=3 then 1 else 0 := by
    simp [tupleTripleFibreValues]
  have hf : (tupleFourFibreValues g b).card=
      ∑ z ∈ tupleBinarySumImage g b,
        if (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=4 then 1 else 0 := by
    simp [tupleFourFibreValues]
  rw [ht,hf,Finset.mul_sum,← Finset.sum_add_distrib,tupleBinaryFibreOvercount]
  apply Finset.sum_congr rfl
  intro z _
  let m := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
  have hm : m ≤ 4 := hcap z
  change Nat.choose (m-1) 2=(if m=3 then 1 else 0)+3*(if m=4 then 1 else 0)
  interval_cases m <;> norm_num

/-- Correction three consists of exactly one four-point value and
no triple values; three isolated triples are ruled out by parity. -/
theorem triple_and_four_counts_of_overcount_eq_three
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hthree : tupleBinaryFibreOvercount g b=3) :
    (tupleTripleFibreValues g b).card=0 ∧ (tupleFourFibreValues g b).card=1 := by
  have hcap := subset_fibre_card_le_four_of_overcount_le_five g b (by omega)
  have he := fibre_overcount_eq_triple_add_three_four_count_of_cap_four g b hcap
  have hp := Nat.even_iff.mp (even_tuple_triple_fibre_count g b)
  omega

/-- The smallest odd correction identifies a unique four-point
midpoint; every other fibre has at most two subsets. No validity is needed. -/
theorem exists_unique_four_point_midpoint_of_overcount_eq_three
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hthree : tupleBinaryFibreOvercount g b=3) :
    ∃ z, (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card=4 ∧
      2 • z=∑ i, (g i+b) ∧ ∀ w, w ≠ z →
        (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card ≤ 2 := by
  classical
  obtain ⟨ht,hf⟩ := triple_and_four_counts_of_overcount_eq_three g b hthree
  have hcap := subset_fibre_card_le_four_of_overcount_le_five g b (by omega)
  have hmem (w : G) (hc : (Finset.univ.filter
      (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card=4) : w ∈ tupleFourFibreValues g b := by
    apply Finset.mem_filter.mpr
    refine ⟨?_,hc⟩
    obtain ⟨U,hU⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter
      (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card)
    exact Finset.mem_image.mpr ⟨U,Finset.mem_univ _,(Finset.mem_filter.mp hU).2⟩
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (by omega : 0 < (tupleFourFibreValues g b).card)
  have hzcard := (Finset.mem_filter.mp hz).2
  have huniq (w : G) (hc : (Finset.univ.filter
      (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card=4) : w=z := by
    exact Finset.card_le_one.mp (by omega : (tupleFourFibreValues g b).card ≤ 1) w (hmem w hc) z hz
  refine ⟨z,hzcard,?_,?_⟩
  · have hc : (Finset.univ.filter (fun U : Finset (Fin n) ↦
        (∑ i ∈ U, (g i+b))=(∑ i, (g i+b))-z)).card=4 := by
      rw [← tuple_binary_fibre_card_eq_complementary_value g b z]
      exact hzcard
    have he := huniq ((∑ i, (g i+b))-z) hc
    rw [two_nsmul]
    exact eq_sub_iff_add_eq.mp he.symm
  · intro w hw
    have hc := hcap w
    by_contra hnot
    rcases (by omega : (Finset.univ.filter
      (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card=3 ∨
      (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card=4) with h3 | h4
    · have hm : w ∈ tupleTripleFibreValues g b := by
        apply Finset.mem_filter.mpr
        refine ⟨?_,h3⟩
        obtain ⟨U,hU⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter
          (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=w)).card)
        exact Finset.mem_image.mpr ⟨U,Finset.mem_univ _,(Finset.mem_filter.mp hU).2⟩
      have hp := Finset.card_pos.mpr ⟨w,hm⟩
      omega
    · exact hw (huniq w h4)

/-- Correction four contains four triple values and no four-point
values, again because the number of triples is even. -/
theorem triple_and_four_counts_of_overcount_eq_four
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hfour : tupleBinaryFibreOvercount g b=4) :
    (tupleTripleFibreValues g b).card=4 ∧ (tupleFourFibreValues g b).card=0 := by
  have hcap := subset_fibre_card_le_four_of_overcount_le_five g b (by omega)
  have he := fibre_overcount_eq_triple_add_three_four_count_of_cap_four g b hcap
  have hp := Nat.even_iff.mp (even_tuple_triple_fibre_count g b)
  omega

end MinModulus
