import MinModulus.CyclicIteratedTargetBounds

namespace MinModulus
open Finset
open scoped Classical

/-- If the next target set is empty, every source still present is
an original escape. No validity or injectivity is needed. -/
theorem iterated_targets_subset_escapes_of_next_empty
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (A : Finset (Fin n)) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hempty : iteratedAffineDoublingTargets g b (k+1)=∅) :
    iteratedAffineDoublingTargets g b k ⊆ A := by
  intro i hi
  by_contra hiA
  obtain ⟨j,hj⟩ := hclosed i hiA
  have hmem : j ∈ iteratedAffineDoublingTargets g b (k+1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,hi,hj⟩
  rw [hempty] at hmem
  exact Finset.notMem_empty _ hmem

/-- An extinct target sequence has a sharper original-escape budget:
the final step pays no doubling cut, giving n <= k|A|+(k-1)|B|. -/
theorem dimension_le_refined_escape_cost_of_targets_empty
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j)
    (hempty : iteratedAffineDoublingTargets g b k=∅) :
    n ≤ k*A.card+(k-1)*B.card := by
  cases k with
  | zero =>
    have h := congrArg Finset.card hempty
    simp only [iteratedAffineDoublingTargets,Finset.card_univ,Fintype.card_fin,Finset.card_empty] at h
    simp only [zero_mul,Nat.zero_sub,add_zero]
    omega
  | succ k =>
    have h := iterated_affine_targets_card_lower_bound g b A B hclosed hinj k
    have hc := Finset.card_le_card (iterated_targets_subset_escapes_of_next_empty g b A hclosed hempty)
    simp only [Nat.add_sub_cancel,Nat.succ_mul,Nat.mul_add] at *
    omega

private theorem two_le_dimension_of_triple_fibre
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b z : G)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    2 ≤ n := by
  have hc := Finset.card_le_univ (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z))
  simp only [Fintype.card_finset,Fintype.card_fin] at hc
  by_contra hn
  have hp : 2^n ≤ (2 : ℕ)^1 := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num only [pow_one] at hp
  omega

/-- Triple fibres force the refined extinction budget at every
admissible target depth. -/
theorem dimension_le_refined_escape_cost_of_triple_fibre
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j)
    (hk : n ≤ 2^k)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    n ≤ k*A.card+(k-1)*B.card := by
  exact dimension_le_refined_escape_cost_of_targets_empty g b A B hclosed hinj
    (iterated_affine_targets_eq_empty_of_triple_fibre g hg b z hk htriple)

/-- The refined original escape-depth threshold rules out every
triple fibre, without an assumed cycle, forest, or rank assignment. -/
theorem subset_fibre_card_le_two_of_refined_escape_depth
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j)
    (hk : n ≤ 2^k) (hsmall : k*A.card+(k-1)*B.card < n) (z : G) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
  by_contra h
  have htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card := by omega
  have hh := dimension_le_refined_escape_cost_of_triple_fibre g hg b z A B hclosed hinj hk htriple
  omega

/-- Below the refined escape-depth threshold, the actual core cube
sum gives the exact intrinsic loss. -/
theorem intrinsic_loss_eq_core_cube_sum_of_refined_escape_depth
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j)
    (hk : n ≤ 2^k) (hsmall : k*A.card+(k-1)*B.card < n) :
    tupleBinaryCollisionLoss g b=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  exact intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b
    (subset_fibre_card_le_two_of_refined_escape_depth g hg b A B hclosed hinj hk hsmall)

/-- With at most one nonzero involution, a triple fibre requires
n+1 <= k(|A|+1), improving the earlier non-strict dimension count. -/
theorem dimension_succ_le_escape_depth_of_one_collision_triple
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (A : Finset (Fin n)) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h) (hk : n ≤ 2^k)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    n+1 ≤ k*(A.card+1) := by
  classical
  have hn := two_le_dimension_of_triple_fibre g b z htriple
  obtain ⟨j,_,hinj⟩ := exists_doubling_injective_compl_outside_protected_set g hg hh hinv ∅
    (by intro i hi; simp at hi) ⟨⟨0,by omega⟩,by simp⟩
  have hb := dimension_le_refined_escape_cost_of_triple_fibre g hg b z A {j} hclosed
    (fun i hi t ht hit ↦ hinj i (by simpa using hi) t (by simpa using ht) hit) hk htriple
  have hkpos : 0 < k := by
    by_contra h
    have hk0 : k=0 := by omega
    rw [hk0,pow_zero] at hk
    omega
  simp only [Finset.card_singleton,Nat.mul_one,Nat.mul_add] at *
  omega

/-- Actual cyclic escapes obey the refined strict density bound
whenever a triple fibre exists, with the cut chosen internally. -/
theorem cyclic_escape_density_strict_of_triple_fibre
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b z : ZMod N)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    n+1 ≤ Nat.clog 2 n*((affineDoublingEscapes g b).card+1) := by
  have hcase {h : ZMod N} (hh : h+h=0) (hinv : ∀ u : ZMod N, u+u=0 → u=0 ∨ u=h) :
      n+1 ≤ Nat.clog 2 n*((affineDoublingEscapes g b).card+1) := by
    apply dimension_succ_le_escape_depth_of_one_collision_triple g hg b z (affineDoublingEscapes g b)
      (affine_double_closed_outside_actual_escapes g b) hh hinv (Nat.le_pow_clog (by decide) n)
    simpa only [Finset.sum_eq_multiset_sum] using htriple
  rcases Nat.even_or_odd N with hev | hod
  · obtain ⟨M,hM⟩ := hev
    have hNM : N=2*M := by omega
    exact hcase (half_add_half hNM) (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hNM u hu)
  · apply hcase (h := 0) (by simp)
    intro u hu
    left
    apply add_self_injective_zmod hod
    simpa using hu

/-- The refined cyclic threshold uses k|A|+(k-1)<n at canonical
depth, with no supplied cut and including tuples of dimensions zero or one. -/
theorem cyclic_subset_fibre_card_le_two_of_refined_actual_escape_cost
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : Nat.clog 2 n*(affineDoublingEscapes g b).card+(Nat.clog 2 n-1) < n) (z : ZMod N) :
    (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card ≤ 2 := by
  by_contra h
  have hb := cyclic_escape_density_strict_of_triple_fibre g hg b z (by omega)
  simp only [Nat.mul_add,Nat.mul_one] at hb
  omega

/-- The refined actual cyclic escape threshold makes the complete
core-cube loss formula exact. -/
theorem cyclic_intrinsic_loss_eq_core_cube_sum_of_refined_escape_cost
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N)
    (hsmall : Nat.clog 2 n*(affineDoublingEscapes g b).card+(Nat.clog 2 n-1) < n) :
    tupleBinaryCollisionLoss g b=
      ∑ uv ∈ tupleBinaryCollisionCores g b, 2^(n-(uv.1 ∪ uv.2).card) := by
  apply intrinsic_loss_eq_binary_core_cube_sum_of_fibres_le_two g hg b
  intro z
  simpa only [Finset.sum_eq_multiset_sum] using
    cyclic_subset_fibre_card_le_two_of_refined_actual_escape_cost g hg b hsmall z

end MinModulus
