import MinModulus.EqualGapCollisionCrossing
import Mathlib.Combinatorics.SetFamily.LYM

namespace MinModulus
open Finset
open scoped Classical

/-- Positive-side inclusion between two actual equal-gap cores forces
the entire cores to coincide. -/
theorem equal_gap_binary_core_eq_of_positive_subset
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (uv pq : Finset (Fin n) × Finset (Fin n))
    (huv : uv ∈ tupleBinaryCollisionCores g b) (hpq : pq ∈ tupleBinaryCollisionCores g b)
    (hgap : uv.1.card-uv.2.card=pq.1.card-pq.2.card) (hsub : uv.1 ⊆ pq.1) : uv=pq := by
  by_contra hne
  have hc := (equal_gap_binary_collision_cores_cross_intersect g hg b uv pq huv hpq hgap hne).2
  have hd := (Finset.mem_filter.mp hpq).2.1
  exact hc ((hd.mono hsub (Finset.Subset.refl _)).symm)

/-- Negative-side inclusion between two actual equal-gap cores likewise
forces equality of both sides. -/
theorem equal_gap_binary_core_eq_of_negative_subset
    {n : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (uv pq : Finset (Fin n) × Finset (Fin n))
    (huv : uv ∈ tupleBinaryCollisionCores g b) (hpq : pq ∈ tupleBinaryCollisionCores g b)
    (hgap : uv.1.card-uv.2.card=pq.1.card-pq.2.card) (hsub : uv.2 ⊆ pq.2) : uv=pq := by
  by_contra hne
  have hc := (equal_gap_binary_collision_cores_cross_intersect g hg b uv pq huv hpq hgap hne).1
  have hd := (Finset.mem_filter.mp hpq).2.1
  exact hc (hd.symm.mono hsub (Finset.Subset.refl _))

/-- Both projections of any actual fixed-gap core family are injective
antichains on the original coordinate set. -/
theorem equal_gap_binary_collision_family_projection_structure
    {n δ : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (F : Finset (Finset (Fin n) × Finset (Fin n))) (hF : F ⊆ tupleBinaryCollisionCores g b)
    (hgap : ∀ uv ∈ F, uv.1.card-uv.2.card=δ) :
    Set.InjOn Prod.fst (↑F : Set (Finset (Fin n) × Finset (Fin n))) ∧
      Set.InjOn Prod.snd (↑F : Set (Finset (Fin n) × Finset (Fin n))) ∧
      IsAntichain (· ⊆ ·) (↑(F.image Prod.fst) : Set (Finset (Fin n))) ∧
      IsAntichain (· ⊆ ·) (↑(F.image Prod.snd) : Set (Finset (Fin n))) := by
  classical
  have hleft (uv) (huv : uv ∈ F) (pq) (hpq : pq ∈ F) (hs : uv.1 ⊆ pq.1) : uv=pq :=
    equal_gap_binary_core_eq_of_positive_subset g hg b uv pq (hF huv) (hF hpq)
      ((hgap uv huv).trans (hgap pq hpq).symm) hs
  have hright (uv) (huv : uv ∈ F) (pq) (hpq : pq ∈ F) (hs : uv.2 ⊆ pq.2) : uv=pq :=
    equal_gap_binary_core_eq_of_negative_subset g hg b uv pq (hF huv) (hF hpq)
      ((hgap uv huv).trans (hgap pq hpq).symm) hs
  refine ⟨?_,?_,?_,?_⟩
  · intro uv huv pq hpq he
    exact hleft uv huv pq hpq (fun i hi ↦ he ▸ hi)
  · intro uv huv pq hpq he
    exact hright uv huv pq hpq (fun i hi ↦ he ▸ hi)
  · intro U hU V hV hne hs
    obtain ⟨uv,huv,rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨pq,hpq,rfl⟩ := Finset.mem_image.mp hV
    exact hne (congrArg Prod.fst (hleft uv huv pq hpq hs))
  · intro U hU V hV hne hs
    obtain ⟨uv,huv,rfl⟩ := Finset.mem_image.mp hU
    obtain ⟨pq,hpq,rfl⟩ := Finset.mem_image.mp hV
    exact hne (congrArg Prod.snd (hright uv huv pq hpq hs))

/-- Every actual fixed-gap collision family satisfies a LYM packing
bound on each side, retaining the individual original side cardinalities. -/
theorem equal_gap_binary_collision_family_lym_bounds
    {n δ : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (F : Finset (Finset (Fin n) × Finset (Fin n))) (hF : F ⊆ tupleBinaryCollisionCores g b)
    (hgap : ∀ uv ∈ F, uv.1.card-uv.2.card=δ) :
    (∑ uv ∈ F, (n.choose uv.1.card : ℚ)⁻¹) ≤ 1 ∧
      (∑ uv ∈ F, (n.choose uv.2.card : ℚ)⁻¹) ≤ 1 := by
  classical
  obtain ⟨hi₁,hi₂,ha₁,ha₂⟩ := equal_gap_binary_collision_family_projection_structure g hg b F hF hgap
  have hlym (f : (Finset (Fin n) × Finset (Fin n)) → Finset (Fin n))
      (hi : Set.InjOn f F) (ha : IsAntichain (· ⊆ ·) (↑(F.image f) : Set (Finset (Fin n)))) :
      (∑ uv ∈ F, (n.choose (f uv).card : ℚ)⁻¹) ≤ 1 := by
    have hh := Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose (𝕜:=ℚ) ha
    simp only [Fintype.card_fin] at hh
    rw [Finset.sum_image (fun a ha b hb he ↦ hi ha hb he)] at hh
    exact hh
  exact ⟨hlym Prod.fst hi₁ ha₁,hlym Prod.snd hi₂ ha₂⟩

/-- The total number of actual cores at any fixed gap is at most
the middle binomial coefficient of the original dimension. -/
theorem equal_gap_binary_collision_family_card_le_middle_binomial
    {n δ : ℕ} {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g) (b : G)
    (F : Finset (Finset (Fin n) × Finset (Fin n))) (hF : F ⊆ tupleBinaryCollisionCores g b)
    (hgap : ∀ uv ∈ F, uv.1.card-uv.2.card=δ) : F.card ≤ n.choose (n/2) := by
  obtain ⟨hi,_,ha,_⟩ := equal_gap_binary_collision_family_projection_structure g hg b F hF hgap
  have hh := ha.sperner
  rw [Finset.card_image_iff.mpr hi] at hh
  simpa only [Fintype.card_fin] using hh

end MinModulus
