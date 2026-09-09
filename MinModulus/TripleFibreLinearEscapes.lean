import MinModulus.TripleFibreAggregateGrowth

namespace MinModulus
open Finset
open scoped Classical

/-- Total binary weight of every complete actual forest is bounded
by twice the dimension minus two at a triple-fibre shift. -/
theorem forest_total_binary_weight_bound_of_triple_fibre
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    (∑ a, (2^(L a)-1))+2 ≤ 2*n := by
  classical
  let r : Fin n → ℕ := fun i ↦ (E.symm i).2.val
  have hr (a : β) (j : Fin (L a)) : r (E ⟨a,j⟩)=j.val := by
    exact congrArg (fun p : Σ a : β, Fin (L a) ↦ p.2.val) (E.symm_apply_apply ⟨a,j⟩)
  have hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b) := by
    intro i hi
    obtain ⟨⟨a,j⟩,rfl⟩ := E.surjective i
    rw [hr] at hi
    let p : Fin (L a) := ⟨j.val-1,by omega⟩
    refine ⟨E ⟨a,p⟩,?_,?_⟩
    · rw [hr,hr]
      dsimp [p]
      omega
    · rw [hchain,hchain,show j.val=p.val+1 by dsimp [p]; omega,pow_succ',mul_smul]
  have h := total_ranked_weight_add_two_le_twice_dimension_of_triple_fibre g hg b z r hp htriple
  have hsum : (∑ i, 2^(r i))=∑ a, (2^(L a)-1) := by
    rw [← Equiv.sum_comp E]
    simp only [Fintype.sum_sigma,hr,sum_binary_powers]
  rwa [hsum] at h

/-- The elementary supporting line at chain lengths two and three
turns exponential arm weight into a uniform linear dimension bound. -/
theorem four_mul_length_le_binary_weight_add_five (m : ℕ) :
    4*m ≤ (2^m-1)+5 := by
  have h := four_mul_le_two_pow_add_four m
  have hp : 0 < (2 : ℕ)^m := pow_pos (by decide) _
  omega

/-- A triple fibre forces at least (2n+2)/5 arms in every complete
actual forest, independently of the maximum arm length. -/
theorem twice_dimension_add_two_le_five_forest_arms_of_triple_fibre
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    2*n+2 ≤ 5*Fintype.card β := by
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hweight := forest_total_binary_weight_bound_of_triple_fibre L g hg E x b z hchain htriple
  have hline := Finset.sum_le_sum (s := Finset.univ)
    (fun a _ ↦ four_mul_length_le_binary_weight_add_five (L a))
  simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,hsize] at hline
  omega

/-- With at most one nonzero involution, a triple fibre forces a
linear number of original escapes, with the one cut paid explicitly. -/
theorem twice_dimension_le_five_escapes_add_three_of_one_collision_triple
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    2*n ≤ 5*(affineDoublingEscapes g b).card+3 := by
  obtain ⟨B,_,hB,L,_,_,E,x,hchain,_⟩ :=
    exists_short_affine_forest_of_one_collision_triple_fibre g hg b z hh hinv htriple
  have h := twice_dimension_add_two_le_five_forest_arms_of_triple_fibre L g hg E x b z hchain htriple
  simp only [Fintype.card_coe] at h
  omega

/-- Injective doubling needs no additional terminal, giving the
stronger linear original-escape bound at every triple-fibre shift. -/
theorem twice_dimension_add_two_le_five_escapes_of_injective_triple
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    2*n+2 ≤ 5*(affineDoublingEscapes g b).card := by
  obtain ⟨L,_,_,E,x,hchain,_⟩ := exists_affine_chain_forest_of_injective_acyclic_doubling
    g hinj (affineDoublingEscapes g b) b (affine_double_closed_outside_actual_escapes g b)
    (fun hm e P ↦ no_affine_cycle_of_triple_fibre hm g hg b z htriple e P)
  simpa only [Fintype.card_coe] using
    twice_dimension_add_two_le_five_forest_arms_of_triple_fibre L g hg E x b z hchain htriple

/-- Every cyclic triple-fibre shift has at least (2n-3)/5 original
escapes, without a forest, cut, or orbit assumption. -/
theorem cyclic_linear_escape_density_of_triple_fibre
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b z : ZMod N)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    2*n ≤ 5*(affineDoublingEscapes g b).card+3 := by
  obtain ⟨B,_,hB,L,_,_,E,x,hchain,_⟩ := exists_short_affine_forest_of_cyclic_triple_fibre g hg b z htriple
  have h := twice_dimension_add_two_le_five_forest_arms_of_triple_fibre L g hg E x b z hchain
    (by simpa only [Finset.sum_eq_multiset_sum] using htriple)
  simp only [Fintype.card_coe] at h
  omega

/-- Odd cyclic doubling is injective, so a triple fibre forces at
least (2n+2)/5 original escapes. -/
theorem odd_cyclic_linear_escape_density_of_triple_fibre
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) (b z : ZMod N)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    2*n+2 ≤ 5*(affineDoublingEscapes g b).card := by
  refine twice_dimension_add_two_le_five_escapes_of_injective_triple g hg b z ?_ ?_
  · intro i j hij
    apply validTuple_injective g hg
    apply add_self_injective_zmod hN
    simpa only [two_nsmul] using hij
  · simpa only [Finset.sum_eq_multiset_sum] using htriple

/-- Below the linear escape threshold all cyclic subset-sum fibres
have multiplicity at most two. -/
theorem cyclic_subset_fibre_card_le_two_of_linear_escape_cost
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 5*(affineDoublingEscapes g b).card+3 < 2*n) (z : ZMod N) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
  by_contra h
  have h := cyclic_linear_escape_density_of_triple_fibre g hg b z (by omega)
  omega

/-- The linear escape threshold supplies exact intrinsic core-cube
accounting for arbitrary cyclic tuples. -/
theorem cyclic_intrinsic_loss_eq_core_cube_sum_of_linear_escape_cost
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 5*(affineDoublingEscapes g b).card+3 < 2*n) :
    tupleBinaryCollisionLoss g b=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  exact intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b
    (fun z ↦ by simpa only [Finset.sum_eq_multiset_sum] using
      cyclic_subset_fibre_card_le_two_of_linear_escape_cost g hg b hsmall z)

end MinModulus
