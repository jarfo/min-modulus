/-
# The crossing star of a dominant canonical collision

Every canonical collision distinct from a fixed source crosses it in at least
one orientation.  Orient each incident pair toward an actual positive-to-
negative crossing.  This gives a weight-preserving injection of the entire
star into the global crossing relation.

Applied to a collision controlling diagonal mass, the star sharpens abstract
concentration to a strict-majority alternative: unless the selected collision
holds more than half of the total canonical padding weight, the crossing star
already controls the squared critical gap.
-/
import MinModulus.G1MinimalSupportFibers

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Orient the pair incident to `r` forward when it is an actual crossing,
and backward otherwise. -/
noncomputable def canonicalCrossPairOrientation
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h := by
  classical
  exact if (r.val.1 ∩ q.val.2).Nonempty then (r, q) else (q, r)

/-- Validity guarantees that the chosen orientation of every distinct
canonical pair is an oriented positive-to-negative crossing. -/
theorem canonicalCrossPairOrientation_mem_crossPairs
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hq : q ∈ canonicalReducedCollisions (g := g) hh)
    (hqr : q ≠ r) :
    canonicalCrossPairOrientation r q ∈
      canonicalPositiveNegativeCrossPairs (g := g) hh := by
  classical
  have hcross := distinct_canonicalReducedCollisions_positive_negative_cross
    g hg hh hh0 r q
      (mem_canonicalReducedCollisions_iff.mp hr)
      (mem_canonicalReducedCollisions_iff.mp hq) hqr
  by_cases hforward : (r.val.1 ∩ q.val.2).Nonempty
  · simp [canonicalCrossPairOrientation, hforward,
      mem_canonicalPositiveNegativeCrossPairs_iff, hr, hq, Ne.symm hqr]
  · have hreverse : (q.val.1 ∩ r.val.2).Nonempty := hcross.resolve_left hforward
    simp [canonicalCrossPairOrientation, hforward,
      mem_canonicalPositiveNegativeCrossPairs_iff, hr, hq, hqr, hreverse]

omit [DecidableEq G] in
/-- Orientation is injective among targets distinct from its fixed center. -/
theorem canonicalCrossPairOrientation_injective_of_ne
    {g : Fin (m + 1) → G} {h : G}
    (r q₁ q₂ : ReducedSubsetSumCollision g h)
    (hq₁ne : q₁ ≠ r) (hq₂ne : q₂ ≠ r)
    (heq : canonicalCrossPairOrientation r q₁ =
      canonicalCrossPairOrientation r q₂) :
    q₁ = q₂ := by
  classical
  by_cases h₁ : (r.val.1 ∩ q₁.val.2).Nonempty <;>
    by_cases h₂ : (r.val.1 ∩ q₂.val.2).Nonempty
  · have heq' : (r, q₁) = (r, q₂) := by
      simpa [canonicalCrossPairOrientation, h₁, h₂] using heq
    exact congrArg Prod.snd heq'
  · have heq' : (r, q₁) = (q₂, r) := by
      simpa [canonicalCrossPairOrientation, h₁, h₂] using heq
    exact False.elim (hq₂ne (congrArg Prod.fst heq').symm)
  · have heq' : (q₁, r) = (r, q₂) := by
      simpa [canonicalCrossPairOrientation, h₁, h₂] using heq
    exact False.elim (hq₁ne (congrArg Prod.fst heq'))
  · have heq' : (q₁, r) = (q₂, r) := by
      simpa [canonicalCrossPairOrientation, h₁, h₂] using heq
    exact congrArg Prod.fst heq'

/-- The oriented crossing star centered at `r`. -/
noncomputable def canonicalCrossStar
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) := by
  classical
  exact ((canonicalReducedCollisions (g := g) hh).erase r).image
    (canonicalCrossPairOrientation r)

/-- Total padding weight away from the center of a canonical crossing star. -/
noncomputable def canonicalCrossStarWeight
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : ℕ := by
  classical
  exact ((canonicalReducedCollisions (g := g) hh).erase r).sum
    (reducedCollisionWeight (m := m))

/-- The whole oriented star lies in the canonical crossing relation. -/
theorem canonicalCrossStar_subset_crossPairs
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh) :
    canonicalCrossStar hh r ⊆
      canonicalPositiveNegativeCrossPairs (g := g) hh := by
  classical
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
  have hq' := Finset.mem_erase.mp hq
  exact canonicalCrossPairOrientation_mem_crossPairs
    g hg hh hh0 r q hr hq'.2 hq'.1

/-- The crossing mass contains the full product-weight star of any canonical
collision. -/
theorem weight_mul_sum_erase_le_canonicalCrossMass
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh) :
    reducedCollisionWeight (m := m) r *
        canonicalCrossStarWeight hh r ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let collisions := canonicalReducedCollisions (g := g) hh
  let weight : ReducedSubsetSumCollision g h → ℕ :=
    reducedCollisionWeight (m := m)
  let pairWeight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦ weight p.1 * weight p.2
  have hinj : Set.InjOn (canonicalCrossPairOrientation r)
      ↑(collisions.erase r) := by
    intro q₁ hq₁ q₂ hq₂ heq
    exact canonicalCrossPairOrientation_injective_of_ne r q₁ q₂
      (Finset.mem_erase.mp hq₁).1 (Finset.mem_erase.mp hq₂).1 heq
  have hsub := canonicalCrossStar_subset_crossPairs g hg hh hh0 r hr
  change weight r * canonicalCrossStarWeight hh r ≤
    (canonicalPositiveNegativeCrossPairs (g := g) hh).sum pairWeight
  calc
    weight r * canonicalCrossStarWeight hh r =
        (collisions.erase r).sum (fun q ↦
          pairWeight (canonicalCrossPairOrientation r q)) := by
      change weight r * (collisions.erase r).sum weight = _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hcross : (r.val.1 ∩ q.val.2).Nonempty
      · simp [pairWeight, weight, canonicalCrossPairOrientation, hcross]
      · simp [pairWeight, weight, canonicalCrossPairOrientation, hcross,
          Nat.mul_comm]
    _ = (canonicalCrossStar hh r).sum pairWeight := by
      symm
      exact Finset.sum_image hinj
    _ ≤ (canonicalPositiveNegativeCrossPairs (g := g) hh).sum pairWeight :=
      Finset.sum_le_sum_of_subset hsub

/-- If `r` controls the squared-gap diagonal term, then either its crossing
star already supplies the fourfold crossing bound, or `r` has strict majority
of the total canonical padding weight. -/
theorem square_le_four_crossMass_or_total_lt_two_weight
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (L : ℕ)
    (hrelative : L * L ≤
      2 * (reducedCollisionWeight (m := m) r *
        (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := m)))) :
    L * L ≤
      4 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) ∨
    (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r := by
  classical
  let collisions := canonicalReducedCollisions (g := g) hh
  let weight : ReducedSubsetSumCollision g h → ℕ :=
    reducedCollisionWeight (m := m)
  let rest := canonicalCrossStarWeight hh r
  have hsum : rest + weight r = collisions.sum weight := by
    simpa [rest, canonicalCrossStarWeight, collisions, weight] using
      Finset.sum_erase_add collisions weight hr
  have hstar := weight_mul_sum_erase_le_canonicalCrossMass
    g hg hh hh0 r hr
  by_cases hmajor : collisions.sum weight < 2 * weight r
  · exact Or.inr hmajor
  · left
    have htwo : 2 * weight r ≤ collisions.sum weight := by omega
    have hwrle : weight r ≤ rest := by omega
    have htotalle : collisions.sum weight ≤ 2 * rest := by omega
    change L * L ≤ 4 *
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        weight p.1 * weight p.2)
    calc
      L * L ≤ 2 * (weight r * collisions.sum weight) := hrelative
      _ ≤ 2 * (weight r * (2 * rest)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (weight r) htotalle)
      _ = 4 * (weight r * rest) := by ring
      _ ≤ 4 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum
          (fun p ↦ weight p.1 * weight p.2) := by
        exact Nat.mul_le_mul_left 4 (by simpa [rest, collisions, weight] using hstar)

end MinModulus
