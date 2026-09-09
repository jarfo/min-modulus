import MinModulus.OddLossFullSupport

namespace MinModulus
open Finset
open scoped Classical

/-- The cardinality of an involution-stable finite set has the same
parity as its fixed-point set. -/
theorem finite_involution_card_mod_two_eq_fixed_card
    {α : Type*} (S : Finset α) (r : α → α)
    (hmem : ∀ a ∈ S, r a ∈ S) (hinv : ∀ a ∈ S, r (r a)=a) :
    S.card%2=(S.filter (fun a ↦ r a=a)).card%2 := by
  classical
  let C := S.filter (fun a ↦ r a ≠ a)
  have hc : Even C.card := by
    apply even_card_of_fixed_point_free_involution_on C r
    · intro a ha
      have hS := (Finset.mem_filter.mp ha).1
      have hne := (Finset.mem_filter.mp ha).2
      apply Finset.mem_filter.mpr
      refine ⟨hmem a hS,?_⟩
      intro he
      rw [hinv a hS] at he
      exact hne he.symm
    · intro a ha
      exact hinv a (Finset.mem_filter.mp ha).1
    · intro a ha
      exact (Finset.mem_filter.mp ha).2
  have hp : (S.filter (fun a ↦ r a=a)).card+C.card=S.card := by
    convert Finset.card_filter_add_card_filter_not (s:=S) (fun a ↦ r a=a) using 1
  have hm := Nat.even_iff.mp hc
  omega

/-- Subset complementation identifies the parity of the actual binary
image with the number of attained halves of its total shifted sum. -/
theorem tuple_binary_image_mod_two_eq_midpoint_count
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    (tupleBinarySumImage g b).card%2=
      ((tupleBinarySumImage g b).filter (fun z ↦ 2 • z=∑ i, (g i+b))).card%2 := by
  classical
  have hp := finite_involution_card_mod_two_eq_fixed_card (tupleBinarySumImage g b)
    (fun z ↦ (∑ i, (g i+b))-z) (total_sub_mem_tuple_binary_image g b)
    (fun z _ ↦ by abel)
  have he : (tupleBinarySumImage g b).filter (fun z ↦ (∑ i, (g i+b))-z=z)=
      (tupleBinarySumImage g b).filter (fun z ↦ 2 • z=∑ i, (g i+b)) := by
    apply Finset.filter_congr
    intro z _
    rw [two_nsmul]
    constructor
    · intro h
      exact eq_sub_iff_add_eq.mp h.symm
    · intro h
      exact (eq_sub_iff_add_eq.mpr h).symm
  rw [he] at hp
  exact hp

/-- In positive dimension, intrinsic loss has the same parity as the
number of attained midpoint values, without validity or a fibre cap. -/
theorem intrinsic_loss_mod_two_eq_midpoint_count
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    tupleBinaryCollisionLoss g b%2=
      ((tupleBinarySumImage g b).filter (fun z ↦ 2 • z=∑ i, (g i+b))).card%2 := by
  have hi := tuple_binary_image_mod_two_eq_midpoint_count g b
  have hc := tuple_binary_image_card_add_loss_eq_two_pow g b
  have he : Even (2^n) := by
    apply even_iff_two_dvd.mpr
    simpa only [pow_one] using pow_dvd_pow 2 (by omega : 1 ≤ n)
  have hm := Nat.even_iff.mp he
  omega

/-- At most two midpoint values can be attained in a cyclic group,
regardless of tuple validity or multiplicity of their subset fibres. -/
theorem cyclic_attained_midpoint_card_le_two
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (b : ZMod N) :
    ((tupleBinarySumImage g b).filter (fun z ↦ 2 • z=∑ i, (g i+b))).card ≤ 2 := by
  classical
  calc
    _ ≤ (Finset.univ.filter (fun z : ZMod N ↦ 2 • z=∑ i, (g i+b))).card := by
      apply Finset.card_le_card
      intro z hz
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2⟩
    _ ≤ 2 := zmod_doubling_fibre_card_le_two _

/-- Odd intrinsic loss has exactly one attained midpoint value at every
nonzero cyclic modulus, without tuple validity or a fibre-size cap. -/
theorem exists_unique_tuple_binary_midpoint_of_cyclic_odd_loss
    {n N : ℕ} [NeZero N] (hn : 0 < n) (g : Fin n → ZMod N) (b : ZMod N)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃! z, z ∈ tupleBinarySumImage g b ∧ 2 • z=∑ i, (g i+b) := by
  classical
  have hp : tupleBinaryCollisionLoss g b%2=
      ((tupleBinarySumImage g b).filter (fun z ↦ 2 • z=∑ i, (g i+b))).card%2 := by
    convert intrinsic_loss_mod_two_eq_midpoint_count hn g b using 1
    congr
  have hc := cyclic_attained_midpoint_card_le_two g b
  have ho := Nat.odd_iff.mp hodd
  have hle : ((tupleBinarySumImage g b).filter (fun z ↦ 2 • z=∑ i, (g i+b))).card ≤ 1 := by omega
  have hpos : 0 < ((tupleBinarySumImage g b).filter (fun z ↦ 2 • z=∑ i, (g i+b))).card := by omega
  obtain ⟨z,hz⟩ := Finset.card_pos.mp hpos
  refine ⟨z,Finset.mem_filter.mp hz,?_⟩
  intro t ht
  exact Finset.card_le_one.mp hle _ (Finset.mem_filter.mpr ht) _ hz

/-- Every full-support relation core has the same positive-side sum
when intrinsic loss is odd, even if the common fibre has many points. -/
theorem exists_common_full_core_sum_of_cyclic_odd_loss
    {n N : ℕ} [NeZero N] (hn : 0 < n) (g : Fin n → ZMod N) (b : ZMod N)
    (hodd : Odd (tupleBinaryCollisionLoss g b)) :
    ∃ z ∈ tupleBinarySumImage g b, 2 • z=∑ i, (g i+b) ∧
      ∀ uv ∈ tupleBinaryCollisionCores g b, uv.1 ∪ uv.2=Finset.univ →
        (∑ i ∈ uv.1, (g i+b))=z := by
  classical
  letI : DecidableEq (ZMod N) := Classical.decEq _
  obtain ⟨z,hz,hunique⟩ := exists_unique_tuple_binary_midpoint_of_cyclic_odd_loss hn g b hodd
  refine ⟨z,hz.1,hz.2,?_⟩
  intro uv huv hfull
  apply hunique
  refine ⟨Finset.mem_image.mpr ⟨uv.1,Finset.mem_univ _,rfl⟩,?_⟩
  exact two_nsmul_full_binary_core_sum_eq_total g b uv huv hfull

/-- Complementation pairs distinct subsets within every midpoint fibre,
so its cardinality is even in positive dimension. -/
theorem even_tuple_binary_midpoint_fibre_card
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (hmid : 2 • z=∑ i, (g i+b)) :
    Even (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card := by
  classical
  apply even_card_of_fixed_point_free_involution_on _ (fun U : Finset (Fin n) ↦ Finset.univ \ U)
  · intro U hU
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ U),(Finset.mem_filter.mp hU).2,← hmid,two_nsmul]
    abel
  · intro U _
    simp
  · intro U _ he
    have hi := Finset.ext_iff.mp he ⟨0,hn⟩
    simp only [Finset.mem_sdiff,Finset.mem_univ,true_and] at hi
    tauto

end MinModulus
