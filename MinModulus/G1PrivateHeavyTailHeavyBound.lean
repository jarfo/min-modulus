/-
# Bounding all private tail-heavy owners

The fixed external-heavy fiber estimate can be propagated through the original
heavy-coordinate split.  Taking the self-heavy threshold to be the exact
self-heavy cardinality eliminates that arm, while three external labels either
consume the available coordinate capacity or produce a fiber larger than the
uniform bound from the joint-gap closure.

Consequently the entire private tail-heavy population is bounded by an
explicit polynomial in the single global self-heavy family, outside the same
three-coordinate capacity alternative.
-/
import MinModulus.G1PrivateHeavyExternalHeavyBound

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Outside three-coordinate capacity, all private tail-heavy owners are
bounded in terms of the global self-heavy family. -/
theorem card_minimalSupportPrivateTailHeavyVertices_le_selfHeavy_or_capacity
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0) :
    let H := (minimalSupportPrivateSelfHeavyVertices g h hmin).card
    let J := H + 6 * (m * (H + 2)) + 2
    let F := H + 1 + 3 * J
    (minimalSupportPrivateTailHeavyVertices g h hmin).card ≤ H + 3 * F ∨
      B.card + 3 ≤ m + 1 := by
  let H := (minimalSupportPrivateSelfHeavyVertices g h hmin).card
  let J := H + 6 * (m * (H + 2)) + 2
  let F := H + 1 + 3 * J
  let T := minimalSupportPrivateTailHeavyVertices g h hmin
  change T.card ≤ H + 3 * F ∨ B.card + 3 ≤ m + 1
  by_cases hbound : T.card ≤ H + 3 * F
  · exact Or.inl hbound
  · have hcount : H + 3 * F < T.card := Nat.lt_of_not_ge hbound
    rcases minimalSupportPrivateHeavy_self_or_capacity_or_largeExternalFiber
        g h hmin H 3 F hcount with hself | hcapacity | hfiber
    · change H < H at hself
      omega
    · exact Or.inr hcapacity
    · obtain ⟨z, _, hzFiber⟩ := hfiber
      rcases card_minimalSupportPrivateExternalHeavyFiber_le_selfHeavy_or_capacity
          g hg h t hh q ht hq hmin hqzero z with hfiberBound | hcapacity
      · have : F <
            (minimalSupportPrivateExternalHeavyFiber g h hmin z).card := by
          simpa [F] using hzFiber
        have : (minimalSupportPrivateExternalHeavyFiber g h hmin z).card ≤ F := by
          simpa [F, J, H] using hfiberBound
        omega
      · exact Or.inr hcapacity

end MinModulus
