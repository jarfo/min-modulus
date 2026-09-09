import MinModulus.IteratedTargetFibreBounds

namespace MinModulus
open Finset
open scoped Classical

/-- Original coordinates whose affine doubles are absent from the tuple. -/
noncomputable def affineDoublingEscapes
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) : Finset (Fin n) :=
  Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)

/-- Every coordinate outside the actual escape set has an actual target. -/
theorem affine_double_closed_outside_actual_escapes
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (b : G) :
    ∀ i, i ∉ affineDoublingEscapes g b → ∃ j, g j=2 • g i+b := by
  intro i hi
  by_contra h
  exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)

/-- Odd cyclic groups need no doubling cut, so their actual escape
count alone determines the canonical intrinsic loss budget. -/
theorem odd_cyclic_intrinsic_loss_le_actual_escape_budget
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N) :
    tupleBinaryCollisionLoss g b ≤ 2^(Nat.clog 2 n*(affineDoublingEscapes g b).card) := by
  apply intrinsic_loss_le_pow_escape_depth_of_injective_doubling g hg b (affineDoublingEscapes g b)
    (affine_double_closed_outside_actual_escapes g b) ?_ (Nat.le_pow_clog (by decide) n)
  intro i j hij
  apply validTuple_injective g hg
  apply add_self_injective_zmod hN
  simpa only [two_nsmul] using hij

/-- Every nonempty cyclic modulus has at most one doubled collision
on a valid tuple; the canonical budget therefore costs one extra escape. -/
theorem cyclic_intrinsic_loss_le_actual_escape_budget
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N) :
    tupleBinaryCollisionLoss g b ≤ 2^(Nat.clog 2 n*((affineDoublingEscapes g b).card+1)) := by
  by_cases hn : 0 < n
  · rcases Nat.even_or_odd N with hev | hod
    · obtain ⟨M,hM⟩ := hev
      have hNM : N=2*M := by omega
      exact intrinsic_loss_le_pow_escape_depth_of_one_collision hn g hg b (affineDoublingEscapes g b)
        (affine_double_closed_outside_actual_escapes g b) (half_add_half hNM)
        (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hNM u hu) (Nat.le_pow_clog (by decide) n)
    · apply (odd_cyclic_intrinsic_loss_le_actual_escape_budget hod g hg b).trans
      apply Nat.pow_le_pow_right (by decide)
      exact Nat.mul_le_mul_left _ (Nat.le_succ _)
  · have hn0 : n=0 := by omega
    subst n
    have h := tuple_binary_image_card_add_loss_eq_two_pow g b
    have hc : Nat.clog 2 0=0 := by decide
    simp only [hc,zero_mul,pow_zero]
    norm_num only [pow_zero] at h
    omega

/-- The original cyclic modulus is bounded by the canonical budget
computed from the tuple's actual escapes at the chosen shift. -/
theorem cyclic_group_card_lower_bound_of_actual_escapes
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N) :
    2^n ≤ N+2^(Nat.clog 2 n*((affineDoublingEscapes g b).card+1)) := by
  have hloss := cyclic_intrinsic_loss_le_actual_escape_budget g hg b
  have himage := Finset.card_le_univ (tupleBinarySumImage g b)
  rw [ZMod.card] at himage
  have hsum := tuple_binary_image_card_add_loss_eq_two_pow g b
  omega

/-- Odd cyclic moduli have the sharper canonical exponent with no
additional cut cost. -/
theorem odd_cyclic_group_card_lower_bound_of_actual_escapes
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N) :
    2^n ≤ N+2^(Nat.clog 2 n*(affineDoublingEscapes g b).card) := by
  have hloss := odd_cyclic_intrinsic_loss_le_actual_escape_budget hN g hg b
  have himage := Finset.card_le_univ (tupleBinarySumImage g b)
  rw [ZMod.card] at himage
  have hsum := tuple_binary_image_card_add_loss_eq_two_pow g b
  omega

/-- A triple fibre forces complete extinction of the actual target
sets by any depth k with n <= 2^k. -/
theorem iterated_affine_targets_eq_empty_of_triple_fibre
    {n k : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (hk : n ≤ 2^k)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    iteratedAffineDoublingTargets g b k=∅ := by
  apply Finset.ext
  intro j
  simp only [Finset.notMem_empty,iff_false]
  intro hj
  have h := subset_fibre_card_le_two_of_iterated_affine_target g hg b hk j hj z
  omega

/-- Triple fibres force a linear lower bound on the original
escape-plus-cut count at ceiling logarithmic depth. -/
theorem dimension_le_canonical_escape_cut_cost_of_triple_fibre
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b z : G)
    (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i=2 • g j → i=j)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    n ≤ Nat.clog 2 n*(A.card+B.card) := by
  have h := iterated_affine_targets_card_lower_bound g b A B hclosed hinj (Nat.clog 2 n)
  rw [iterated_affine_targets_eq_empty_of_triple_fibre g hg b z (Nat.le_pow_clog (by decide) n) htriple,
    Finset.card_empty,zero_add] at h
  exact h

/-- Every triple fibre over a cyclic group requires many actual
escapes; no forest, cut, or rank data is an input. -/
theorem cyclic_escape_density_of_triple_fibre
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g) (b z : ZMod N)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    n ≤ Nat.clog 2 n*((affineDoublingEscapes g b).card+1) := by
  classical
  by_cases hn : 0 < n
  · have hcase {h : ZMod N} (hh : h+h=0) (hinv : ∀ u : ZMod N, u+u=0 → u=0 ∨ u=h) :
        n ≤ Nat.clog 2 n*((affineDoublingEscapes g b).card+1) := by
      obtain ⟨j,_,hinj⟩ := exists_doubling_injective_compl_outside_protected_set g hg hh hinv ∅
        (by intro i hi; simp at hi) ⟨⟨0,hn⟩,by simp⟩
      simpa only [Finset.card_singleton] using dimension_le_canonical_escape_cut_cost_of_triple_fibre
        g hg b z (affineDoublingEscapes g b) {j} (affine_double_closed_outside_actual_escapes g b)
        (fun i hi t ht hit ↦ hinj i (by simpa using hi) t (by simpa using ht) hit)
        (by simpa only [Finset.sum_eq_multiset_sum] using htriple)
    rcases Nat.even_or_odd N with hev | hod
    · obtain ⟨M,hM⟩ := hev
      have hNM : N=2*M := by omega
      exact hcase (half_add_half hNM) (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hNM u hu)
    · apply hcase (h := 0) (by simp)
      intro u hu
      left
      apply add_self_injective_zmod hod
      simpa using hu
  · omega

/-- In odd cyclic groups, triple fibres require n <= ceil(log2 n)
times the actual escape count, with no extra cut term. -/
theorem odd_cyclic_escape_density_of_triple_fibre
    {n N : ℕ} [NeZero N] (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) (b z : ZMod N)
    (htriple : 2 < (Finset.univ.filter (fun U : Finset (Fin n) ↦ (∑ i ∈ U, (g i+b))=z)).card) :
    n ≤ Nat.clog 2 n*(affineDoublingEscapes g b).card := by
  simpa only [Finset.card_empty,add_zero] using dimension_le_canonical_escape_cut_cost_of_triple_fibre
    g hg b z (affineDoublingEscapes g b) ∅ (affine_double_closed_outside_actual_escapes g b)
    (by
      intro i _ j _ hij
      apply validTuple_injective g hg
      apply add_self_injective_zmod hN
      simpa only [two_nsmul] using hij)
    (by simpa only [Finset.sum_eq_multiset_sum] using htriple)

end MinModulus
