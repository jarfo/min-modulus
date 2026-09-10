import MinModulus.FibreGrowthSaturation
import MinModulus.FibreMultiplicityEscapeDensity

namespace MinModulus
open Finset
open scoped Classical

/-- Total binary weight of every complete actual forest is bounded
by twice the dimension minus three at a triple-fibre shift. -/
theorem forest_total_binary_weight_add_three_bound_of_triple_fibre
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    (∑ a, (2^(L a)-1))+3 ≤ 2*n := by
  obtain ⟨r,hp,hsum⟩ := exists_global_ranks_of_actual_forest L g E x b hchain
  have h := total_ranked_weight_add_three_le_twice_dimension_of_triple_fibre g hg b z r hp htriple
  rwa [hsum] at h

/-- A triple fibre forces at least (2n+3)/5 arms in every complete
actual forest, independently of the maximum arm length. -/
theorem twice_dimension_add_three_le_five_forest_arms_of_triple_fibre
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    2*n+3 ≤ 5*Fintype.card β := by
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hweight := forest_total_binary_weight_add_three_bound_of_triple_fibre L g hg E x b z hchain htriple
  have hline := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ ↦ four_mul_length_le_binary_weight_add_five (L a))
  simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,hsize] at hline
  omega

/-- Every cyclic triple-fibre shift has at least (2n-2)/5 original
escapes, without a forest, cut, or orbit assumption. -/
theorem cyclic_parity_refined_escape_density_of_triple_fibre
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b z : ZMod N)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    2*n ≤ 5*(affineDoublingEscapes g b).card+2 := by
  obtain ⟨B,_,hB,L,_,_,E,x,hchain,_⟩ := exists_short_affine_forest_of_cyclic_triple_fibre g hg b z htriple
  have h := twice_dimension_add_three_le_five_forest_arms_of_triple_fibre L g hg E x b z hchain
    (by simpa only [Finset.sum_eq_multiset_sum] using htriple)
  simp only [Fintype.card_coe] at h
  omega

/-- Odd cyclic tuples need no cut, and the parity-refined bound
forces at least (2n+3)/5 original escapes at every triple fibre. -/
theorem odd_cyclic_parity_refined_escape_density_of_triple_fibre
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) (b z : ZMod N)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    2*n+3 ≤ 5*(affineDoublingEscapes g b).card := by
  have hinj : Function.Injective (fun i ↦ 2 • g i) := by
    intro i j hij
    apply validTuple_injective g hg
    apply add_self_injective_zmod hN
    simpa only [two_nsmul] using hij
  obtain ⟨L,_,_,E,x,hchain,_⟩ := exists_affine_chain_forest_of_injective_acyclic_doubling
    g hinj (affineDoublingEscapes g b) b (affine_double_closed_outside_actual_escapes g b)
    (fun hm e P ↦ no_affine_cycle_of_triple_fibre hm g hg b z
      (by simpa only [Finset.sum_eq_multiset_sum] using htriple) e P)
  simpa only [Fintype.card_coe] using
    twice_dimension_add_three_le_five_forest_arms_of_triple_fibre L g hg E x b z hchain
      (by simpa only [Finset.sum_eq_multiset_sum] using htriple)

/-- Below the parity-refined escape threshold all cyclic subset-sum fibres
have multiplicity at most two. -/
theorem cyclic_subset_fibre_card_le_two_of_parity_refined_escape_cost
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 5*(affineDoublingEscapes g b).card+2 < 2*n) (z : ZMod N) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
  by_contra h
  have h := cyclic_parity_refined_escape_density_of_triple_fibre g hg b z (by omega)
  omega

/-- The parity-refined escape threshold supplies exact intrinsic core-cube
accounting for arbitrary cyclic tuples. -/
theorem cyclic_intrinsic_loss_eq_core_cube_sum_of_parity_refined_escape_cost
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 5*(affineDoublingEscapes g b).card+2 < 2*n) :
    tupleBinaryCollisionLoss g b=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  exact intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b
    (fun z ↦ by simpa only [Finset.sum_eq_multiset_sum] using
      cyclic_subset_fibre_card_le_two_of_parity_refined_escape_cost g hg b hsmall z)

/-- The odd-modulus escape threshold includes the old equality case. -/
theorem odd_cyclic_subset_fibre_card_le_two_of_parity_refined_escape_cost
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 5*(affineDoublingEscapes g b).card < 2*n+3) (z : ZMod N) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
  by_contra h
  have hh := odd_cyclic_parity_refined_escape_density_of_triple_fibre hN g hg b z (by omega)
  omega

/-- At odd moduli the improved escape criterion gives exact core-cube
loss accounting, without a supplied forest or cycle hypothesis. -/
theorem odd_cyclic_intrinsic_loss_eq_core_sum_of_parity_refined_escape_cost
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 5*(affineDoublingEscapes g b).card < 2*n+3) :
    tupleBinaryCollisionLoss g b=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  exact intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b
    (fun z ↦ by simpa only [Finset.sum_eq_multiset_sum] using
      odd_cyclic_subset_fibre_card_le_two_of_parity_refined_escape_cost hN g hg b hsmall z)

end MinModulus
