import MinModulus.GeneralFibreLossCorrection
import MinModulus.TripleFibreCorrectionParity

namespace MinModulus
open Finset
open scoped Classical

/-- Pairing finite weights under an involution gives an even sum when
fixed points have weight zero. The finite lifting retains every copy. -/
theorem even_weighted_sum_of_involution_with_zero_fixed_weights
    {α : Type*} (S : Finset α) (r : α → α) (w : α → ℕ)
    (hmem : ∀ a ∈ S, r a ∈ S) (hinv : ∀ a ∈ S, r (r a)=a)
    (hw : ∀ a ∈ S, w (r a)=w a) (hz : ∀ a ∈ S, r a=a → w a=0) :
    Even (∑ a ∈ S, w a) := by
  classical
  let T := S.sigma (fun a ↦ Finset.range (w a))
  have he : Even T.card := by
    apply even_card_of_fixed_point_free_involution_on T
      (fun p : Σ _ : α, ℕ ↦ ⟨r p.1,p.2⟩)
    · intro p hp
      obtain ⟨ha,hi⟩ := Finset.mem_sigma.mp hp
      apply Finset.mem_sigma.mpr
      refine ⟨hmem p.1 ha,?_⟩
      rw [hw p.1 ha]
      exact hi
    · intro p hp
      have ha := (Finset.mem_sigma.mp hp).1
      change (⟨r (r p.1),p.2⟩ : Σ _ : α, ℕ)=p
      rw [hinv p.1 ha]
    · intro p hp heq
      obtain ⟨ha,hi⟩ := Finset.mem_sigma.mp hp
      have hr : r p.1=p.1 := congrArg Sigma.fst heq
      have hzero := hz p.1 ha hr
      have hlt := Finset.mem_range.mp hi
      omega
  simpa only [T,Finset.card_sigma,Finset.card_range] using he

/-- Only midpoint fibres can obstruct evenness of the full correction;
if all of them have size at most two, complement pairing gives evenness. -/
theorem even_fibre_overcount_of_midpoint_fibres_le_two
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hcap : ∀ z, 2 • z=∑ i, (g i+b) →
      (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2) :
    Even (tupleBinaryFibreOvercount g b) := by
  classical
  unfold tupleBinaryFibreOvercount
  apply even_weighted_sum_of_involution_with_zero_fixed_weights
    (tupleBinarySumImage g b) (fun z ↦ (∑ i, (g i+b))-z)
    (fun z ↦ Nat.choose ((Finset.univ.filter
      (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card-1) 2)
  · exact total_sub_mem_tuple_binary_image g b
  · intro z _
    abel
  · intro z _
    rw [← tuple_binary_fibre_card_eq_complementary_value g b z]
  · intro z _ he
    have hmid : 2 • z=∑ i, (g i+b) := by
      rw [two_nsmul]
      exact eq_sub_iff_add_eq.mp he.symm
    have h := hcap z hmid
    exact Nat.choose_eq_zero_of_lt (by omega)

/-- In positive dimension, an odd total correction requires an attained
midpoint with at least four subsets, without a validity assumption. -/
theorem exists_four_point_midpoint_of_odd_fibre_overcount
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hodd : Odd (tupleBinaryFibreOvercount g b)) :
    ∃ z ∈ tupleBinarySumImage g b, 2 • z=∑ i, (g i+b) ∧
      4 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card := by
  classical
  by_contra h
  push Not at h
  have hcap : ∀ z, 2 • z=∑ i, (g i+b) →
      (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
    intro z hmid
    by_contra hnot
    obtain ⟨U,hU⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter
      (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    have hz : z ∈ tupleBinarySumImage g b :=
      Finset.mem_image.mpr ⟨U,Finset.mem_univ _,(Finset.mem_filter.mp hU).2⟩
    have hm := Nat.even_iff.mp (even_tuple_binary_midpoint_fibre_card hn g b z hmid)
    have hl := h z hz hmid
    omega
  have hev := Nat.even_iff.mp (even_fibre_overcount_of_midpoint_fibres_le_two g b hcap)
  have hod := Nat.odd_iff.mp hodd
  omega

/-- The intrinsic half-exponent threshold makes the full correction
even, although other subset-sum fibres may still contain triples. -/
theorem even_fibre_overcount_of_intrinsic_half_exponent
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (hsmall : 2*Nat.log 2 (tupleBinaryCollisionLoss g b) < n) :
    Even (tupleBinaryFibreOvercount g b) := by
  exact even_fibre_overcount_of_midpoint_fibres_le_two g b
    (fun z hz ↦ midpoint_fibre_card_le_two_of_intrinsic_half_exponent g b z hsmall hz)

/-- Under the intrinsic half-exponent threshold, the total core charge
and actual loss have equal parity without a global fibre-size cap. -/
theorem intrinsic_loss_mod_two_eq_core_sum_of_half_exponent
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (hsmall : 2*Nat.log 2 (tupleBinaryCollisionLoss g b) < n) :
    tupleBinaryCollisionLoss g b%2=
      (∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card))%2 := by
  have he := intrinsic_loss_add_fibre_overcount_eq_core_cube_sum g hg b
  have hp := Nat.even_iff.mp (even_fibre_overcount_of_intrinsic_half_exponent g b hsmall)
  omega

end MinModulus
