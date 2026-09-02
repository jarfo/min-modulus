/-
# Closing the dense joint gap/omission branch

The joint source/target split says that a sufficiently dense fixed
`(gap,omission)` fiber either exposes three external coordinates or, after
normalizing the gap to the common heavy coordinate, has many heavy targets.

The fresh-gap level argument bounds that normalized heavy-target family by
`m * (selfHeavy + 2)` outside the same capacity conclusion.  Substituting
this value as the target threshold closes the dense terminal branch outright.
-/
import MinModulus.G1PrivateHeavyJointGapFreshFibers

namespace MinModulus

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- A joint fixed-gap/common-omission fiber denser than the remaining source
threshold plus the normalized heavy-target bound forces three-coordinate
ambient capacity. -/
theorem minimalSupportPrivateJointGap_dense_card_add_three_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (A : ℕ)
    (hcount :
      (A + m * ((minimalSupportPrivateSelfHeavyVertices
          g h hmin).card + 2)) *
        (minimalSupportPrivateJointGapOmissionVertices
          g hg h t hh q ht hq hmin hqzero z e delta w).card <
      (minimalSupportPrivateJointGapOmissionFiber
        g hg h t hh q ht hq hmin hqzero z e delta w).card) :
    B.card + 3 ≤ m + 1 := by
  let C := m * ((minimalSupportPrivateSelfHeavyVertices g h hmin).card + 2)
  have hsplit := minimalSupportPrivateJointGap_capacity_three_or_manyHeavyAtFixed
    g hg h t hh q ht hq hmin hqzero z e delta w A C (by
      simpa [C] using hcount)
  rcases hsplit with hcapacity | ⟨hfixed, hmany⟩
  · exact hcapacity
  · have hbound :=
      card_minimalSupportPrivateJointGapHeavyTargetVertices_le_levels_mul_selfHeavy_or_capacity
        g hg h t hh q ht hq hmin hqzero z e delta w hfixed
    rcases hbound with hheavy | hcapacity
    · change C <
          (minimalSupportPrivateJointGapHeavyTargetVertices
            g hg h t hh q ht hq hmin hqzero z e delta w).card at hmany
      change (minimalSupportPrivateJointGapHeavyTargetVertices
          g hg h t hh q ht hq hmin hqzero z e delta w).card ≤ C at hheavy
      omega
    · exact hcapacity

end MinModulus
