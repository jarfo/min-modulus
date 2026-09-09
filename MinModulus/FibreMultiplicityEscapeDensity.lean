import MinModulus.FibreMultiplicityGrowth
import MinModulus.TripleFibreLinearEscapes

namespace MinModulus
open Finset
open scoped Classical

/-- An actual complete forest supplies global predecessor ranks whose
coordinate weights sum to the binary arm weights. -/
theorem exists_global_ranks_of_actual_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    ∃ r : Fin n → ℕ,
      (∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ g i+b=2 • (g j+b)) ∧
      (∑ i, 2^(r i))=∑ a, (2^(L a)-1) := by
  classical
  let r : Fin n → ℕ := fun i ↦ (E.symm i).2.val
  have hr (a : β) (j : Fin (L a)) : r (E ⟨a,j⟩)=j.val := by
    exact congrArg (fun p : Σ a : β, Fin (L a) ↦ p.2.val) (E.symm_apply_apply ⟨a,j⟩)
  refine ⟨r,?_,?_⟩
  · intro i hi
    obtain ⟨⟨a,j⟩,rfl⟩ := E.surjective i
    rw [hr] at hi
    let p : Fin (L a) := ⟨j.val-1,by omega⟩
    refine ⟨E ⟨a,p⟩,?_,?_⟩
    · rw [hr,hr]
      dsimp [p]
      omega
    · rw [hchain,hchain,show j.val=p.val+1 by dsimp [p]; omega,pow_succ',mul_smul]
  · rw [← Equiv.sum_comp E]
    simp only [Fintype.sum_sigma,hr,sum_binary_powers]

/-- Binary arm weight plus the number of arms is at least twice
the total number of vertices, including zero-length numerical arms. -/
theorem twice_total_length_le_binary_weight_add_arm_count
    {β : Type*} [Fintype β] (L : β → ℕ) :
    2*(∑ a, L a) ≤ (∑ a, (2^(L a)-1))+Fintype.card β := by
  have hpoint (a : β) : 2*L a ≤ (2^(L a)-1)+1 := by
    have h := Nat.mul_le_pow (by decide : 2 ≠ 1) (L a)
    have hp : 0 < (2 : ℕ)^(L a) := pow_pos (by decide) _
    omega
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hpoint a)
  simpa only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,smul_eq_mul,mul_one] using h

/-- Multiplicity m at least three forces (m-3)n+m-1 <= (m-2)r
for every complete actual forest with r arms. -/
theorem fibre_multiplicity_forest_arm_count_bound
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (htriple : 3 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    let m := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
    (m-3)*n+(m-1) ≤ (m-2)*Fintype.card β := by
  classical
  let m := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
  change 3 ≤ m at htriple
  change (m-3)*n+(m-1) ≤ (m-2)*Fintype.card β
  obtain ⟨r,hp,hsum⟩ := exists_global_ranks_of_actual_forest L g E x b hchain
  have h := fibre_card_sub_two_mul_growth_tax_bound g hg b z r hp (by omega)
  change (m-2)*((∑ i, 2^(r i))-n)+m-1 ≤ n at h
  rw [Nat.add_sub_assoc (by omega : 1 ≤ m)] at h
  have hbase := dimension_le_total_ranked_weight r
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hline := twice_total_length_le_binary_weight_add_arm_count L
  rw [hsize,← hsum] at hline
  have htax : n ≤ (∑ i, 2^(r i))-n+Fintype.card β := by omega
  have hm := Nat.mul_le_mul_left (m-2) htax
  have hstep : m-2=(m-3)+1 := by omega
  nlinarith only [h,hm,hstep]

/-- Four equal-sum subsets force at least (n+3)/2 arms in every
complete actual forest. -/
theorem dimension_add_three_le_twice_forest_arms_of_four_fibre
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hfour : 4 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    n+3 ≤ 2*Fintype.card β := by
  classical
  obtain ⟨r,hp,hsum⟩ := exists_global_ranks_of_actual_forest L g E x b hchain
  have h := fibre_card_sub_two_mul_growth_tax_bound g hg b z r hp (by omega)
  let m := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
  let T := (∑ i, 2^(r i))-n
  change 4 ≤ m at hfour
  change (m-2)*T+m-1 ≤ n at h
  rw [Nat.add_sub_assoc (by omega : 1 ≤ m)] at h
  have hbase := dimension_le_total_ranked_weight r
  have hsize : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hline := twice_total_length_le_binary_weight_add_arm_count L
  rw [hsize,← hsum] at hline
  have htax : n ≤ T+Fintype.card β := by dsimp [T]; omega
  have hmul := Nat.mul_le_mul_right T (by omega : 2 ≤ m-2)
  have hsmall : 2*T+3 ≤ n := by omega
  omega

/-- At cyclic fibre multiplicity m>=3, original escapes satisfy
(m-3)n+1 <= (m-2)|A|; the single cut is absorbed explicitly. -/
theorem cyclic_escape_density_of_fibre_multiplicity
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b z : ZMod N)
    (htriple : 3 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    let m := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
    (m-3)*n+1 ≤ (m-2)*(affineDoublingEscapes g b).card := by
  classical
  let m := (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card
  change 3 ≤ m at htriple
  change (m-3)*n+1 ≤ (m-2)*(affineDoublingEscapes g b).card
  obtain ⟨B,_,hB,L,_,_,E,x,hchain,_⟩ := exists_short_affine_forest_of_cyclic_triple_fibre g hg b z (by omega)
  have h := fibre_multiplicity_forest_arm_count_bound L g hg E x b z hchain
    (by simpa only [m,Finset.sum_eq_multiset_sum] using htriple)
  have h' : (m-3)*n+(m-1) ≤ (m-2)*Fintype.card B := by
    simpa only [m,Finset.sum_eq_multiset_sum] using h
  simp only [Fintype.card_coe] at h'
  have hmul := Nat.mul_le_mul_left (m-2) hB
  have hstep : m-1=(m-2)+1 := by omega
  nlinarith only [h',hmul,hstep]

/-- Four-point cyclic fibres force more than half the coordinates
to be original escapes, up to the integer rounding. -/
theorem cyclic_half_escape_density_of_four_fibre
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b z : ZMod N)
    (hfour : 4 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    n+1 ≤ 2*(affineDoublingEscapes g b).card := by
  obtain ⟨B,_,hB,L,_,_,E,x,hchain,_⟩ := exists_short_affine_forest_of_cyclic_triple_fibre g hg b z (by omega)
  have h := dimension_add_three_le_twice_forest_arms_of_four_fibre L g hg E x b z hchain
    (by simpa only [Finset.sum_eq_multiset_sum] using hfour)
  simp only [Fintype.card_coe] at h
  omega

/-- Four-point odd cyclic fibres need no cut, so n+3 <= 2|A|. -/
theorem odd_cyclic_half_escape_density_of_four_fibre
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) (b z : ZMod N)
    (hfour : 4 ≤ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    n+3 ≤ 2*(affineDoublingEscapes g b).card := by
  have hinj : Function.Injective (fun i ↦ 2 • g i) := by
    intro i j hij
    apply validTuple_injective g hg
    apply add_self_injective_zmod hN
    simpa only [two_nsmul] using hij
  have htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card := by omega
  obtain ⟨L,_,_,E,x,hchain,_⟩ := exists_affine_chain_forest_of_injective_acyclic_doubling
    g hinj (affineDoublingEscapes g b) b (affine_double_closed_outside_actual_escapes g b)
    (fun hm e P ↦ no_affine_cycle_of_triple_fibre hm g hg b z
      (by simpa only [Finset.sum_eq_multiset_sum] using htriple) e P)
  simpa only [Fintype.card_coe] using dimension_add_three_le_twice_forest_arms_of_four_fibre
    L g hg E x b z hchain (by simpa only [Finset.sum_eq_multiset_sum] using hfour)

/-- At most half as many original escapes as coordinates excludes
all cyclic fibres of multiplicity four or more. -/
theorem cyclic_subset_fibre_card_le_three_of_half_escape_cost
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : 2*(affineDoublingEscapes g b).card ≤ n) (z : ZMod N) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 3 := by
  by_contra h
  have h := cyclic_half_escape_density_of_four_fibre g hg b z (by omega)
  omega

end MinModulus
