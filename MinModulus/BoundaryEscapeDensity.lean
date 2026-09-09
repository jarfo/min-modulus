import MinModulus.PredecessorClosedOutsideLoss
import MinModulus.CollisionForest

namespace MinModulus
open Finset
open scoped Classical

/-- The supporting linear bound through binary chain lengths two and
three controls the number of arms in a narrow forest. -/
theorem four_mul_le_two_pow_add_four (l : ℕ) : 4*l ≤ 2^l+4 := by
  by_cases h : l < 2
  · interval_cases l <;> norm_num
  · have hl : 2 ≤ l := by omega
    clear h
    induction l,hl using Nat.le_induction with
    | base => norm_num
    | succ l hl ih =>
      have hp : 4 ≤ (2 : ℕ)^l := by
        have hh := Nat.pow_le_pow_right (by decide : 0 < 2) hl
        simpa using hh
      rw [pow_succ]
      nlinarith

/-- Every actual positive forest at the valid sharp midpoint boundary
has binary diameter strictly below twice the dimension minus one. -/
theorem boundary_forest_diameter_lt_twice_dimension
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    (∑ a, (2^(L a)-1)) < 2*n-1 := by
  by_contra h
  have hwide : 2*n-1 ≤ ∑ a, (2^(L a)-1) := by omega
  apply profile_rectangles_not_pairwise_disjoint_at_midpoint_boundary L hL g hg E x b z hchain hmid hlarge hboundary
  intro w hw v hv hne
  exact forestProfileLowerBox_disjoint_of_ne L hL hwide g hg E x b hchain w v hw hv hne

/-- Every actual positive boundary forest needs at least the chain
count expressed by 2*n+2 ≤ 5*r. -/
theorem boundary_forest_chain_count_lower_bound
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b z : G)
    (hchain : ∀ a (j : Fin (L a)), g (E ⟨a,j⟩)+b=2^j.val • x a)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    2*n+2 ≤ 5*Fintype.card β := by
  have hdiam := boundary_forest_diameter_lt_twice_dimension L hL g hg E x b z hchain hmid hlarge hboundary
  have htotal : (∑ a, L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hpoint : ∀ a, 4*L a ≤ (2^(L a)-1)+5 := by
    intro a
    have hh := four_mul_le_two_pow_add_four (L a)
    have hp : 0 < 2^(L a) := by positivity
    omega
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun a _ ↦ hpoint a)
  simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,htotal] at hs
  omega

/-- The cycle exclusion extracts an actual affine forest indexed by
any proposed escape set whenever doubling on the original tuple is
injective. Every endpoint and all original coordinates are retained. -/
theorem exists_actual_affine_forest_at_injective_midpoint_boundary
    {n : ℕ} (hn : 4 ≤ n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (b z : G)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    ∃ L : A → ℕ, (∀ a, 0 < L a) ∧ (∑ a, L a)=n ∧
      ∃ E : (Σ a : A, Fin (L a)) ≃ Fin n, ∃ x : A → G,
        (∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) ∧
        (∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val) := by
  simpa only [Fintype.card_fin] using exists_affine_chain_forest_of_injective_acyclic_doubling g hinj A b hclosed
    (fun hm e R ↦ not_affine_doubling_cycle_at_midpoint_boundary hn hm g hg b z hmid hlarge hboundary e R)

/-- Injective actual doubling at the valid boundary forces the escape
bound 2*n+2 ≤ 5*|A|, with no forest supplied as a hypothesis. -/
theorem boundary_injective_escape_count_lower_bound
    {n : ℕ} (hn : 4 ≤ n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (b z : G)
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    2*n+2 ≤ 5*A.card := by
  obtain ⟨L,hL,_,E,x,hchain,_⟩ := exists_actual_affine_forest_at_injective_midpoint_boundary hn g hg hinj A b z hclosed hmid hlarge hboundary
  simpa only [Fintype.card_coe] using boundary_forest_chain_count_lower_bound L hL g hg E x b z hchain hmid hlarge hboundary

/-- If the ambient group has at most one nonzero involution, cutting
at most one doubled collision gives 2*n+2 ≤ 5*(|A|+1) for the exact
actual escape set at a valid boundary. -/
theorem boundary_escape_count_lower_bound_of_one_collision
    {n : ℕ} (hn : 4 ≤ n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (A : Finset (Fin n)) (b z : G)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b)
    (hmid : 2 • z=∑ i, (g i+b))
    (hlarge : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card)
    (hboundary : tupleBinaryCollisionLoss g b+1=2^(n/2)+2^(n-n/2)) :
    2*n+2 ≤ 5*(A.card+1) := by
  obtain ⟨B,_,hB,L,hL,E,x,hchain,_,_,_⟩ :=
    exists_affine_forest_with_longest_genuine_arm_of_one_collision (by omega : 0 < n) g hg hh hinv A b hA
      (fun hm e R ↦ not_affine_doubling_cycle_at_midpoint_boundary hn hm g hg b z hmid hlarge hboundary e R)
  have hc := boundary_forest_chain_count_lower_bound L hL g hg E x b z hchain hmid hlarge hboundary
  simp only [Fintype.card_coe] at hc
  omega

end MinModulus
