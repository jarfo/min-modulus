/-
# Crossing mass versus diagonal padding concentration

The dense canonical crossing relation becomes quantitative after separating
the square of the total padding weight into its off-diagonal and diagonal
parts.  The off-diagonal part is exactly the product weight of ordered
distinct canonical pairs, and crossing density captures at least half of it.

Consequently the square of the total canonical weight is bounded by twice
the oriented crossing mass plus the diagonal sum of squared weights.  A
simple dichotomy then says that either four times the crossing mass already
controls the square, or twice the diagonal mass does.  This isolates the
only possible concentration loss in the crossing branch.
-/
import MinModulus.G1CanonicalCrossing

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The ordered-distinct product weight plus the diagonal squared weight is
exactly the square of the total canonical padding weight. -/
theorem sum_canonicalDistinctPairWeights_add_diagonal_eq_square
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) :
    (canonicalDistinctReducedCollisionPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
      (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r) =
      (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := m)) *
        (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := m)) := by
  classical
  let collisions := canonicalReducedCollisions (g := g) hh
  let weight : ReducedSubsetSumCollision g h → ℕ :=
    reducedCollisionWeight (m := m)
  let pairWeight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦ weight p.1 * weight p.2
  have hdistinct :
      canonicalDistinctReducedCollisionPairs (g := g) hh =
        collisions.offDiag := by
    ext p
    simp [canonicalDistinctReducedCollisionPairs, collisions, and_assoc]
  change (canonicalDistinctReducedCollisionPairs (g := g) hh).sum pairWeight +
      collisions.sum (fun r ↦ weight r * weight r) =
    collisions.sum weight * collisions.sum weight
  rw [hdistinct]
  calc
    collisions.offDiag.sum pairWeight +
        collisions.sum (fun r ↦ weight r * weight r) =
      collisions.offDiag.sum pairWeight + collisions.diag.sum pairWeight := by
        rw [Finset.sum_diag]
    _ = collisions.diag.sum pairWeight + collisions.offDiag.sum pairWeight :=
      Nat.add_comm _ _
    _ = (collisions.diag ∪ collisions.offDiag).sum pairWeight :=
      (Finset.sum_union (Finset.disjoint_diag_offDiag collisions)).symm
    _ = (collisions ×ˢ collisions).sum pairWeight := by
      rw [Finset.diag_union_offDiag]
    _ = collisions.sum weight * collisions.sum weight := by
      rw [Finset.sum_product]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- Crossing density controls the full square of canonical padding weight up
to the explicit diagonal concentration term. -/
theorem square_sum_canonicalWeights_le_two_crossMass_add_diagonal
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := m)) *
        (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := m)) ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) +
        (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
          reducedCollisionWeight (m := m) r *
            reducedCollisionWeight (m := m) r) := by
  have hdensity :=
    sum_canonicalDistinctPairWeights_le_two_mul_crossPairWeights
      g hg hh hh0
  have hsplit :=
    sum_canonicalDistinctPairWeights_add_diagonal_eq_square
      (g := g) hh
  omega

/-- Quantitative branch split: either crossing mass controls the squared
total weight, or the diagonal squared weights are genuinely concentrated. -/
theorem square_sum_canonicalWeights_le_four_crossMass_or_two_diagonal
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := m)) *
        (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := m)) ≤
      4 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) ∨
    (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := m)) *
        (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := m)) ≤
      2 * (canonicalReducedCollisions (g := g) hh).sum (fun r ↦
        reducedCollisionWeight (m := m) r *
          reducedCollisionWeight (m := m) r) := by
  have htotal := square_sum_canonicalWeights_le_two_crossMass_add_diagonal
    g hg hh hh0
  omega

end MinModulus
