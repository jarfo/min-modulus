/-
# Back-propagating the dense joint-gap closure

The dense `(gap,omission)` closure is pushed backward through the two exact
label-fiber counts.  Two omission labels suffice to pay the gap coordinate
and reach three-coordinate capacity; three external gap labels suffice at the
preceding layer.

Consequently every joint heavy/escape owner family has an explicit bound in
terms of the global self-heavy family, unless three coordinates already remain
outside the deletion set.
-/
import MinModulus.G1PrivateHeavyJointGapClosure

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- An external directed-gap fiber above the joint owner family closes by
three-coordinate capacity once it exceeds twice the downstream dense-fiber
threshold. -/
theorem minimalSupportPrivateJointExternalGap_dense_card_add_three_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta : Fin (m + 1))
    (hcount : let S := (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e)
      let C := m * ((minimalSupportPrivateSelfHeavyVertices g h hmin).card + 2)
      2 * (C * S.card) <
        (minimalSupportSelectedPrivateExternalGapFiber
          g hg h hmin S delta).card) :
    B.card + 3 ≤ m + 1 := by
  let S := minimalSupportPrivateJointExternalHeavyEscapeOwners
    g hg h t q ht hq hmin hqzero z e
  let C := m * ((minimalSupportPrivateSelfHeavyVertices g h hmin).card + 2)
  change 2 * (C * S.card) <
    (minimalSupportSelectedPrivateExternalGapFiber
      g hg h hmin S delta).card at hcount
  rcases
      minimalSupportPrivateJointExternalGapOmission_capacity_or_largeFiber
        g hg h t hh q ht hq hmin hqzero z e delta 2 (C * S.card) hcount with
    hcapacity | hfiber
  · omega
  · obtain ⟨w, _, _, hpairs⟩ := hfiber
    let V := minimalSupportPrivateJointGapOmissionVertices
      g hg h t hh q ht hq hmin hqzero z e delta w
    have hV : V.card ≤ S.card := by
      calc
        V.card ≤ (Finset.univ : Finset ↥S).card :=
          Finset.card_le_card (Finset.subset_univ V)
        _ = S.card := by simp
    have hdense : (0 + C) * V.card <
        (minimalSupportPrivateJointGapOmissionFiber
          g hg h t hh q ht hq hmin hqzero z e delta w).card := by
      have hmul : C * V.card ≤ C * S.card := Nat.mul_le_mul_left C hV
      exact lt_of_le_of_lt (by simpa using hmul) hpairs
    exact minimalSupportPrivateJointGap_dense_card_add_three_le
      g hg h t hh q ht hq hmin hqzero z e delta w 0 hdense

/-- Outside three-coordinate capacity, every joint heavy/escape owner family
is explicitly bounded by the global self-heavy family and the ambient number
of coefficient levels. -/
theorem card_minimalSupportPrivateJointExternalHeavyEscapeOwners_le_selfHeavy_or_capacity
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e : Fin (m + 1)) :
    let S := minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e
    let H := (minimalSupportPrivateSelfHeavyVertices g h hmin).card
    let C := m * (H + 2)
    S.card ≤ H + 6 * C + 2 ∨ B.card + 3 ≤ m + 1 := by
  let S := minimalSupportPrivateJointExternalHeavyEscapeOwners
    g hg h t q ht hq hmin hqzero z e
  let H := (minimalSupportPrivateSelfHeavyVertices g h hmin).card
  let C := m * (H + 2)
  change S.card ≤ H + 6 * C + 2 ∨ B.card + 3 ≤ m + 1
  by_cases hbound : S.card ≤ H + 6 * C + 2
  · exact Or.inl hbound
  · right
    have hSpos : 0 < S.card := by omega
    have hcoef : H + 1 + 6 * C < S.card - 1 := by omega
    have hmul : (H + 1 + 6 * C) * S.card <
        (S.card - 1) * S.card :=
      (Nat.mul_lt_mul_right hSpos).2 hcoef
    let R := 2 * (C * S.card)
    have hpairs : (H + 1) * S.card + 3 * R <
        S.card * (S.card - 1) := by
      calc
        (H + 1) * S.card + 3 * R =
            (H + 1 + 6 * C) * S.card := by simp [R]; ring
        _ < (S.card - 1) * S.card := hmul
        _ = S.card * (S.card - 1) := Nat.mul_comm _ _
    rcases
        minimalSupportPrivateJointFiber_selfHeavy_or_capacity_or_largeExternalGapFiber
          g hg h t q ht hq hmin hqzero z e (H + 1) 3 R hpairs with
      hself | hcapacity | hgap
    · change H + 1 ≤ H at hself
      omega
    · exact hcapacity
    · obtain ⟨delta, _, hdelta⟩ := hgap
      exact minimalSupportPrivateJointExternalGap_dense_card_add_three_le
        g hg h t hh q ht hq hmin hqzero z e delta (by
          simpa [R, C] using hdelta)

end MinModulus
