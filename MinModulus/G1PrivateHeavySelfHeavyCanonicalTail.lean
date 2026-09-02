/-
# Canonical negative-tail charge from a self-heavy omission star

Canonical reduced collisions orient their two sides so that the positive side
is no larger than the negative side.  Consequently the sign ambiguity in the
tail-light output of the star split costs nothing: even when the star
omissions become the canonical left side, they also fit in the canonical
right side.

This places the entire light branch on the negative-tail side used throughout
the existing attachment, padding, and crossing machinery.
-/
import MinModulus.G1PrivateHeavySelfHeavyStarLightHeavy
import MinModulus.G1LargeSupportUpperFacePacking

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A cardinality charge into a collision's negative tail becomes an
exponential positive-upper-face charge after the possible anchor loss. -/
theorem pow_pred_mul_reducedCollisionWeight_le_positiveUpper_card_of_le_right_add_one
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (q : ReducedSubsetSumCollision g h) (k : ℕ)
    (hk : k ≤ q.val.2.card + 1) :
    2 ^ (k - 1) * reducedCollisionWeight (m := m) q ≤
      (blockedSignatureUpperValueLayer g q.val.1).card := by
  have hexponent : k - 1 ≤ q.val.2.card := by omega
  rw [← pow_negativeCard_mul_reducedCollisionWeight_eq_positiveUpper_card
    hg q]
  exact Nat.mul_le_mul_right (reducedCollisionWeight (m := m) q)
    (Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hexponent)

/-- The exact-two self-heavy star either is small, charges the canonical
negative tail of one collision (up to the unavoidable anchor loss), or
produces a genuinely tail-heavy witness while retaining its full omission
reservoir. -/
theorem card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_largeCanonicalNegativeTail_or_tailHeavy
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h : G) (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ x : G, x + x = 0 → x = 0 ∨ x = h)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) :
    (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤ 3 ∨
      ∃ z : Fin (m + 1), z ∉ B ∧
        supportAvoidingWitnessAt g hno z z = 0 ∧
        (minimalSupportPrivateSelfHeavyExactTwoVertices g h hmin).card ≤
          (witnessOmissionCoordinates
            (supportAvoidingWitnessAt g hno z)).card ∧
        ((∃ r : ReducedSubsetSumCollision g h,
            r ∈ canonicalReducedCollisions (g := g) hh ∧
              (minimalSupportPrivateSelfHeavyExactTwoVertices
                g h hmin).card ≤ r.val.2.card + 1 ∧
              2 ^ ((minimalSupportPrivateSelfHeavyExactTwoVertices
                    g h hmin).card - 1) *
                  reducedCollisionWeight (m := m) r ≤
                (blockedSignatureUpperValueLayer g r.val.1).card ∧
              (subsetCollisionCoeffs r.val.1 r.val.2 =
                  supportAvoidingWitnessAt g hno z ∨
                subsetCollisionCoeffs r.val.1 r.val.2 =
                  -supportAvoidingWitnessAt g hno z)) ∨
          ∃ k : Fin m,
            2 ≤ supportAvoidingWitnessAt g hno z k.succ) := by
  rcases
      card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_canonicalSide_or_tailHeavy
        g hg h hh hne hunique hmin hno with
    hsmall | ⟨z, hzB, hz0, hreservoir, hlight | hheavy⟩
  · exact Or.inl hsmall
  · right
    refine ⟨z, hzB, hz0, hreservoir, Or.inl ?_⟩
    rcases hlight with ⟨r, hr, ⟨hcoeff, hcard⟩ | ⟨hcoeff, hcard⟩⟩
    · exact ⟨r, hr, hcard,
        pow_pred_mul_reducedCollisionWeight_le_positiveUpper_card_of_le_right_add_one
          g hg r _ hcard,
        Or.inl hcoeff⟩
    · have hcanonical := (mem_canonicalReducedCollisions_iff).mp hr
      have hside : r.val.1.card + 1 ≤ r.val.2.card + 1 :=
        Nat.add_le_add_right (canonicalReducedCollision_card_le hcanonical) 1
      have hright := le_trans hcard hside
      exact ⟨r, hr, hright,
        pow_pred_mul_reducedCollisionWeight_le_positiveUpper_card_of_le_right_add_one
          g hg r _ hright,
        Or.inr hcoeff⟩
  · exact Or.inr ⟨z, hzB, hz0, hreservoir, Or.inr hheavy⟩

end MinModulus
