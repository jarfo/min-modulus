import MinModulus.CollisionSeparatingPermutationCount
import MinModulus.CollisionHeavyEscapeBound

namespace MinModulus
open Finset
open scoped Classical

/-- The largest support-binomial cube charge compatible with dimension,
positive-side cardinality gap, and a lower bound on support size. -/
def binaryCollisionGapChargeEnvelope (n δ lower : ℕ) : ℕ :=
  ((Finset.range (n+1)).filter (fun u ↦ δ ≤ u ∧ 2*u-δ ≤ n ∧ lower ≤ 2*u-δ)).sup
    (fun u ↦ 2^(n-(2*u-δ)) * (2*u-δ).choose u)

/-- A pointwise bound on binomial-weighted core charges bounds the sum of
all complementary cube charges at one gap, regardless of family size. -/
theorem equal_gap_binary_core_cube_sum_le_of_binomial_bound
    {n δ B : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (F : Finset (Finset (Fin n) × Finset (Fin n))) (hF : F ⊆ tupleBinaryCollisionCores g b)
    (hgap : ∀ uv ∈ F, uv.1.card - uv.2.card = δ)
    (hB : ∀ uv ∈ F, 2^(n-(uv.1 ∪ uv.2).card) *
      (uv.1.card + uv.2.card).choose uv.1.card ≤ B) :
    (∑ uv ∈ F, 2^(n-(uv.1 ∪ uv.2).card)) ≤ B := by
  have hpack := equal_gap_binary_collision_family_support_lym_bound g hg b F hF hgap
  have hpoint : ∀ uv ∈ F, (2^(n-(uv.1 ∪ uv.2).card) : ℚ) ≤
      B * ((uv.1.card + uv.2.card).choose uv.1.card : ℚ)⁻¹ := by
    intro uv huv
    have hc : (0 : ℚ) < (uv.1.card + uv.2.card).choose uv.1.card := by
      exact_mod_cast Nat.choose_pos (by omega : uv.1.card ≤ uv.1.card + uv.2.card)
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ hc).mpr
    exact_mod_cast hB uv huv
  have hsum : (∑ uv ∈ F, (2^(n-(uv.1 ∪ uv.2).card) : ℚ)) ≤ B := by
    calc
      _ ≤ ∑ uv ∈ F, (B : ℚ) * ((uv.1.card + uv.2.card).choose uv.1.card : ℚ)⁻¹ :=
        Finset.sum_le_sum hpoint
      _ = (B : ℚ) * ∑ uv ∈ F, ((uv.1.card + uv.2.card).choose uv.1.card : ℚ)⁻¹ :=
        (Finset.mul_sum ..).symm
      _ ≤ (B : ℚ) * 1 := mul_le_mul_of_nonneg_left hpack (Nat.cast_nonneg B)
      _ = B := mul_one _
  exact_mod_cast hsum

/-- Actual fixed-gap core volume is bounded by a finite binomial envelope
using only dimension, gap, and a support-size lower bound. -/
theorem equal_gap_binary_core_cube_sum_le_support_envelope
    {n δ lower : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (F : Finset (Finset (Fin n) × Finset (Fin n))) (hF : F ⊆ tupleBinaryCollisionCores g b)
    (hgap : ∀ uv ∈ F, uv.1.card - uv.2.card = δ)
    (hlower : ∀ uv ∈ F, lower ≤ (uv.1 ∪ uv.2).card) :
    (∑ uv ∈ F, 2^(n-(uv.1 ∪ uv.2).card)) ≤ binaryCollisionGapChargeEnvelope n δ lower := by
  apply equal_gap_binary_core_cube_sum_le_of_binomial_bound g hg b F hF hgap
  intro uv huv
  obtain ⟨hd,_,hlt⟩ := (Finset.mem_filter.mp (hF huv)).2
  have hs := Finset.card_union_of_disjoint hd
  have hdim : (uv.1 ∪ uv.2).card ≤ n := by simpa using Finset.card_le_univ (uv.1 ∪ uv.2)
  have hu : uv.1.card ≤ n := by simpa using Finset.card_le_univ uv.1
  have hδ := hgap uv huv
  have hl := hlower uv huv
  have he : 2*uv.1.card-δ = (uv.1 ∪ uv.2).card := by omega
  have hm : uv.1.card ∈ (Finset.range (n+1)).filter
      (fun u ↦ δ ≤ u ∧ 2*u-δ ≤ n ∧ lower ≤ 2*u-δ) := by
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  have h := Finset.le_sup (f := fun u ↦ 2^(n-(2*u-δ)) * (2*u-δ).choose u) hm
  simpa only [he,hs,binaryCollisionGapChargeEnvelope] using h

/-- A supplied doubling cut turns the original escape count into a support
lower bound, hence an explicit binomial envelope for each collision gap. -/
theorem equal_gap_binary_core_cube_sum_le_envelope_with_doubling_cut
    {n δ : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (A B : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j = 2 • g i + b)
    (hinj : ∀ i, i ∉ B → ∀ j, j ∉ B → 2 • g i = 2 • g j → i = j)
    (F : Finset (Finset (Fin n) × Finset (Fin n)))
    (hF : F ⊆ tupleBinaryCollisionCores g b)
    (hgap : ∀ uv ∈ F, uv.1.card - uv.2.card = δ) :
    (∑ uv ∈ F, 2^(n-(uv.1 ∪ uv.2).card)) ≤
      binaryCollisionGapChargeEnvelope n δ (n+1-2*δ-A.card-B.card) := by
  apply equal_gap_binary_core_cube_sum_le_support_envelope g hg b F hF hgap
  intro uv huv
  obtain ⟨hd,he,hlt⟩ := (Finset.mem_filter.mp (hF huv)).2
  have h := heavier_collision_card_lower_bound_with_doubling_cut g hg b uv.1 uv.2 A B he hlt hclosed hinj
  have hs := Finset.card_union_of_disjoint hd
  have hδ := hgap uv huv
  omega

/-- With at most one nonzero involution, original escapes alone bound the
support envelope; no actual forest or injectivity cut is supplied. -/
theorem equal_gap_binary_core_cube_sum_le_envelope_of_one_collision
    {n δ : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (A : Finset (Fin n))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j = 2 • g i + b)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (F : Finset (Finset (Fin n) × Finset (Fin n))) (hF : F ⊆ tupleBinaryCollisionCores g b)
    (hgap : ∀ uv ∈ F, uv.1.card - uv.2.card = δ) :
    (∑ uv ∈ F, 2^(n-(uv.1 ∪ uv.2).card)) ≤
      binaryCollisionGapChargeEnvelope n δ (n-2*δ-A.card) := by
  apply equal_gap_binary_core_cube_sum_le_support_envelope g hg b F hF hgap
  intro uv huv
  obtain ⟨hd,he,hlt⟩ := (Finset.mem_filter.mp (hF huv)).2
  have h := heavier_collision_card_lower_bound_of_one_collision g hg b uv.1 uv.2 A he hlt hclosed hh hinv
  have hs := Finset.card_union_of_disjoint hd
  have hδ := hgap uv huv
  omega

end MinModulus
