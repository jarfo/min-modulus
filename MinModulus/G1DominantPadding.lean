/-
# Dominant padding shape from diagonal concentration

The diagonal branch in the crossing-mass dichotomy cannot remain an abstract
sum of squares.  The total canonical padding weight is at most half the group
order, because twice that weight is exactly the half-translate overlap.  A
maximum-weight canonical collision also bounds the diagonal squared-weight
sum by its weight times the total weight.

Together these statements turn diagonal concentration into one explicit
reduced collision whose power-of-two padding multiplicity is large.
-/
import MinModulus.G1CrossingMass

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- Twice the total canonical padding weight is at most the ambient group
order: it is exactly the cardinality of a subset-sum/translate overlap. -/
theorem two_mul_sum_canonicalWeights_le_card
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    2 * (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) ≤ Fintype.card G := by
  rw [← card_subsetSumOverlap_eq_two_mul_canonical_weights g hg hh hh0]
  exact Finset.card_le_univ _

omit [Fintype G] [DecidableEq G] in
/-- Padding weight is reverse-monotone in reduced support size. -/
theorem reducedCollision_support_card_le_of_weight_le
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hweight : reducedCollisionWeight (m := m) q ≤
      reducedCollisionWeight (m := m) r) :
    (r.val.1 ∪ r.val.2).card ≤ (q.val.1 ∪ q.val.2).card := by
  have hrle : (r.val.1 ∪ r.val.2).card ≤ m := by
    simpa using Finset.card_le_univ (r.val.1 ∪ r.val.2)
  have hexp : m - (q.val.1 ∪ q.val.2).card ≤
      m - (r.val.1 ∪ r.val.2).card :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp
      (by simpa [reducedCollisionWeight] using hweight)
  exact (Nat.sub_le_sub_iff_left hrle).mp hexp

omit [Fintype G] in
/-- In a nonempty canonical family, a maximum-weight collision controls the
whole diagonal squared-weight sum by its weight times the total weight. -/
theorem exists_canonical_weight_mul_sum_ge_diagonal
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (hne : (canonicalReducedCollisions (g := g) hh).Nonempty) :
    ∃ r ∈ canonicalReducedCollisions (g := g) hh,
      (∀ q ∈ canonicalReducedCollisions (g := g) hh,
        reducedCollisionWeight (m := m) q ≤
          reducedCollisionWeight (m := m) r) ∧
      (∀ q ∈ canonicalReducedCollisions (g := g) hh,
        (r.val.1 ∪ r.val.2).card ≤ (q.val.1 ∪ q.val.2).card) ∧
        (canonicalReducedCollisions (g := g) hh).sum (fun q ↦
            reducedCollisionWeight (m := m) q *
              reducedCollisionWeight (m := m) q) ≤
          reducedCollisionWeight (m := m) r *
            (canonicalReducedCollisions (g := g) hh).sum
              (reducedCollisionWeight (m := m)) := by
  classical
  let collisions := canonicalReducedCollisions (g := g) hh
  let weight : ReducedSubsetSumCollision g h → ℕ :=
    reducedCollisionWeight (m := m)
  obtain ⟨r, hr, hrmax⟩ := Finset.exists_max_image collisions weight hne
  refine ⟨r, hr, hrmax, ?_, ?_⟩
  · intro q hq
    exact reducedCollision_support_card_le_of_weight_le r q (hrmax q hq)
  change collisions.sum (fun q ↦ weight q * weight q) ≤
    weight r * collisions.sum weight
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro q hq
  exact Nat.mul_le_mul_right (weight q) (hrmax q hq)

end MinModulus
