import MinModulus.ProfileRectangleInjectivity

namespace MinModulus
open Finset
open scoped Classical

/-- The only point of a singleton profile rectangle is a corner of the
ordinary forest box, including any zero-length coordinates. -/
theorem singleton_profile_lower_box_point_is_corner
    {β : Type*} [Fintype β] (L : β → ℕ) (w : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hc : (forestProfileLowerBox L w).card=1)
    (q : ∀ i, Fin (2^(L i))) (hq : q ∈ forestProfileLowerBox L w) :
    ∀ i, (q i).val=0 ∨ (q i).val=2^(L i)-1 := by
  obtain ⟨s,t,_,ht,_,htval⟩ := exists_profile_lower_box_extreme_points L w
  have htq : t=q := Finset.card_le_one.mp hc.le _ ht _ hq
  have hw := singleton_profile_lower_box_coordinate_eq_double L w hc q hq
  intro i
  have hi := htval i
  rw [htq] at hi
  have hwi := hw i
  omega

/-- A bounded profile rectangle is a singleton exactly when every
profile coordinate is at an endpoint of its doubled interval. -/
theorem profile_lower_box_card_eq_one_iff_endpoint_coordinates
    {β : Type*} [Fintype β] (L : β → ℕ) (w : ∀ i, Fin (2*(2^(L i)-1)+1)) :
    (forestProfileLowerBox L w).card=1 ↔
      ∀ i, (w i).val=0 ∨ (w i).val=2*(2^(L i)-1) := by
  constructor
  · intro hc
    obtain ⟨q,hq⟩ := Finset.card_pos.mp (by omega : 0 < (forestProfileLowerBox L w).card)
    have hcorner := singleton_profile_lower_box_point_is_corner L w hc q hq
    have hw := singleton_profile_lower_box_coordinate_eq_double L w hc q hq
    intro i
    rcases hcorner i with h | h
    · left
      rw [hw i,h,mul_zero]
    · right
      rw [hw i,h]
  · intro hw
    rw [forestProfileLowerBox_card]
    apply Finset.prod_eq_one
    intro i _
    have hi := hw i
    omega

/-- A chain digit is maximal exactly when the original subset contains
every coordinate of that chain. -/
theorem forest_subset_digit_max_iff
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (U : Finset (Fin n)) (a : β) :
    (forestSubsetDigits L E U a).val=2^(L a)-1 ↔ ∀ j : Fin (L a), E ⟨a,j⟩ ∈ U := by
  classical
  have hfull : (∑ j : Fin (L a), (2 : ℕ)^j.val)=2^(L a)-1 := by
    rw [Fin.sum_univ_eq_sum_range]
    exact sum_two_pow (L a)
  constructor
  · intro hd j
    have hs : Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U)=Finset.univ := by
      apply finset_fin_binary_weight_injective (L a)
      change (forestSubsetDigits L E U a).val=(∑ j : Fin (L a), 2^j.val)
      rw [hd,hfull]
    have hj : j ∈ Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U) := by
      rw [hs]
      exact Finset.mem_univ _
    exact (Finset.mem_filter.mp hj).2
  · intro h
    change (∑ j ∈ Finset.univ.filter (fun j : Fin (L a) ↦ E ⟨a,j⟩ ∈ U), 2^j.val)=2^(L a)-1
    simpa only [h,Finset.filter_true] using hfull

/-- The negative subset's actual digit point belongs to its core's
profile rectangle. -/
theorem binary_core_negative_digits_mem_profile_lower_box
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (uv : tupleBinaryCollisionCores g b) :
    forestSubsetDigits L E uv.val.2 ∈
      forestProfileLowerBox L (binaryCoreForestProfile L hL g hg E x b hchain uv).val := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,fun a ↦ ?_⟩
  have hid := binary_core_forest_profile_coordinate_eq L hL g hg E x b hchain uv a
  have hu := (forestSubsetDigits L E uv.val.1 a).isLt
  omega

/-- If an actual core's profile rectangle is a singleton, every original
chain lies wholly on one side of the core. -/
theorem binary_core_whole_chains_of_singleton_profile
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (uv : tupleBinaryCollisionCores g b)
    (hc : (forestProfileLowerBox L (binaryCoreForestProfile L hL g hg E x b hchain uv).val).card=1) :
    ∀ a, (∀ j : Fin (L a), E ⟨a,j⟩ ∈ uv.val.1 ∧ E ⟨a,j⟩ ∉ uv.val.2) ∨
      (∀ j : Fin (L a), E ⟨a,j⟩ ∈ uv.val.2 ∧ E ⟨a,j⟩ ∉ uv.val.1) := by
  have hend := (profile_lower_box_card_eq_one_iff_endpoint_coordinates L _).mp hc
  intro a
  have hid := binary_core_forest_profile_coordinate_eq L hL g hg E x b hchain uv a
  have hu := (forestSubsetDigits L E uv.val.1 a).isLt
  have hv := (forestSubsetDigits L E uv.val.2 a).isLt
  rcases hend a with h | h
  · left
    have hU : (forestSubsetDigits L E uv.val.1 a).val=2^(L a)-1 := by omega
    have hV : (forestSubsetDigits L E uv.val.2 a).val=0 := by omega
    intro j
    exact ⟨(forest_subset_digit_max_iff L E uv.val.1 a).mp hU j,
      (forest_subset_digit_zero_iff L E uv.val.2 a).mp hV j⟩
  · right
    have hU : (forestSubsetDigits L E uv.val.1 a).val=0 := by omega
    have hV : (forestSubsetDigits L E uv.val.2 a).val=2^(L a)-1 := by omega
    intro j
    exact ⟨(forest_subset_digit_max_iff L E uv.val.2 a).mp hV j,
      (forest_subset_digit_zero_iff L E uv.val.1 a).mp hU j⟩

/-- Every full-support core at the valid sharp midpoint boundary
separates complete original chains into its positive and negative sides. -/
theorem boundary_full_support_core_whole_chains
    {n : ℕ} (hn : 4 ≤ n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2))
    (uv : tupleBinaryCollisionCores g b) (hfull : uv.val.1 ∪ uv.val.2=Finset.univ) :
    ∀ a, (∀ j : Fin (L a), E ⟨a,j⟩ ∈ uv.val.1 ∧ E ⟨a,j⟩ ∉ uv.val.2) ∨
      (∀ j : Fin (L a), E ⟨a,j⟩ ∈ uv.val.2 ∧ E ⟨a,j⟩ ∉ uv.val.1) := by
  apply binary_core_whole_chains_of_singleton_profile L hL g hg E x b hchain uv
  have hc := boundary_profile_lower_box_card_eq_core_charge hn L hL g hg E x b z hchain hmid hlarge hboundary uv
  simpa only [hfull,Finset.card_univ,Fintype.card_fin,Nat.sub_self,pow_zero] using hc

end MinModulus
