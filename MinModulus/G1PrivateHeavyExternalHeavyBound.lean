/-
# Bounding external-heavy fibers after joint-gap closure

An owner escape inside a fixed external-heavy fiber forces coefficient at
least two at the private owner, because the protected quarter witness vanishes
on the deletion set.  Except for the anchor, the heavy-coordinate selector is
therefore normalized to that owner.  This injects owner escapes into the global
self-heavy family with the familiar one-anchor loss.

The remaining external-escape arm is split into joint `(heavy,escape)` fibers,
which are bounded by the back-propagated joint-gap theorem.  Hence every fixed
external-heavy fiber receives an explicit bound in terms of self-heavy mass.
-/
import MinModulus.G1PrivateHeavyJointGapBackprop

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Selecting the private owner as escape forces the witness coefficient at
that owner to be at least two. -/
theorem minimalSupportPrivateExternalHeavyOwnerEscape_ownerHeavy
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1))
    {b : ↥(minimalSupportPrivateTailHeavyVertices g h hmin)}
    (hb : b ∈ minimalSupportPrivateExternalHeavyOwnerEscapeVertices
      g hg h t q ht hq hmin hqzero z) :
    2 ≤ minimalSupportPrivateWitness g h hmin b.val b.val := by
  have howner := (Finset.mem_filter.mp hb).2
  have hescape := (mem_minimalSupportPrivateEscapePairs_iff
    g h q hmin b.val
      (minimalSupportPrivateHeavyEscapeCoordinate
        g hg h t q ht hq hmin hqzero b)).mp
      (minimalSupportPrivateHeavyEscapeCoordinate_mem
        g hg h t q ht hq hmin hqzero b)
  have hqb := hqzero b.val b.val.property
  rw [howner, hqb] at hescape
  omega

/-- Embed a non-anchor owner escape into the global self-heavy family. -/
noncomputable def minimalSupportPrivateExternalHeavyOwnerEscapeToSelfHeavy
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1))
    (b : ↥(minimalSupportPrivateExternalHeavyOwnerEscapeVertices
      g hg h t q ht hq hmin hqzero z))
    (hb0 : b.val.val.val ≠ 0) :
    ↥(minimalSupportPrivateSelfHeavyVertices g h hmin) := by
  refine ⟨b.val, (mem_minimalSupportPrivateSelfHeavyVertices_iff
    g h hmin b.val).mpr ?_⟩
  exact minimalSupportPrivateHeavyCoordinate_eq_owner_of_nonzero_ownerHeavy
    g h hmin b.val hb0
      (minimalSupportPrivateExternalHeavyOwnerEscape_ownerHeavy
        g hg h t q ht hq hmin hqzero z b.property)

@[simp] theorem minimalSupportPrivateExternalHeavyOwnerEscapeToSelfHeavy_val
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1))
    (b : ↥(minimalSupportPrivateExternalHeavyOwnerEscapeVertices
      g hg h t q ht hq hmin hqzero z))
    (hb0 : b.val.val.val ≠ 0) :
    (minimalSupportPrivateExternalHeavyOwnerEscapeToSelfHeavy
      g hg h t q ht hq hmin hqzero z b hb0).val = b.val := by
  rfl

/-- At most the anchor is lost when owner escapes are normalized globally. -/
theorem card_minimalSupportPrivateExternalHeavyOwnerEscapeVertices_le_selfHeavy_add_one
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1)) :
    (minimalSupportPrivateExternalHeavyOwnerEscapeVertices
      g hg h t q ht hq hmin hqzero z).card ≤
      (minimalSupportPrivateSelfHeavyVertices g h hmin).card + 1 := by
  classical
  let O := minimalSupportPrivateExternalHeavyOwnerEscapeVertices
    g hg h t q ht hq hmin hqzero z
  let H := minimalSupportPrivateSelfHeavyVertices g h hmin
  let enc : ↥O → Option ↥H := fun b ↦
    if hb0 : b.val.val.val = 0 then none
    else some (minimalSupportPrivateExternalHeavyOwnerEscapeToSelfHeavy
      g hg h t q ht hq hmin hqzero z b hb0)
  have henc : Function.Injective enc := by
    intro b u hbu
    by_cases hb0 : b.val.val.val = 0
    · have hu0 : u.val.val.val = 0 := by
        by_contra hu0
        simp [enc, hb0, hu0] at hbu
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hb0.trans hu0.symm
    · have hu0 : u.val.val.val ≠ 0 := by
        intro hu0
        simp [enc, hb0, hu0] at hbu
      have hself :
          minimalSupportPrivateExternalHeavyOwnerEscapeToSelfHeavy
              g hg h t q ht hq hmin hqzero z b hb0 =
            minimalSupportPrivateExternalHeavyOwnerEscapeToSelfHeavy
              g hg h t q ht hq hmin hqzero z u hu0 := by
        simpa [enc, hb0, hu0] using hbu
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x ↦ x.val.val) hself
  have hcard := Fintype.card_le_of_injective enc henc
  change O.card ≤ H.card + 1
  calc
    O.card = Fintype.card ↥O := (Fintype.card_coe O).symm
    _ ≤ Fintype.card (Option ↥H) := hcard
    _ = H.card + 1 := by simp

/-- Outside three-coordinate capacity, every fixed external-heavy fiber is
bounded by its owner escapes plus three copies of the joint-fiber bound. -/
theorem card_minimalSupportPrivateExternalHeavyFiber_le_selfHeavy_or_capacity
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z : Fin (m + 1)) :
    let H := (minimalSupportPrivateSelfHeavyVertices g h hmin).card
    let J := H + 6 * (m * (H + 2)) + 2
    (minimalSupportPrivateExternalHeavyFiber g h hmin z).card ≤
        H + 1 + 3 * J ∨
      B.card + 3 ≤ m + 1 := by
  let H := (minimalSupportPrivateSelfHeavyVertices g h hmin).card
  let J := H + 6 * (m * (H + 2)) + 2
  let F := minimalSupportPrivateExternalHeavyFiber g h hmin z
  change F.card ≤ H + 1 + 3 * J ∨ B.card + 3 ≤ m + 1
  by_cases hbound : F.card ≤ H + 1 + 3 * J
  · exact Or.inl hbound
  · right
    have hcount : H + 1 + 3 * J < F.card := Nat.lt_of_not_ge hbound
    rcases
        minimalSupportPrivateExternalHeavyFiber_ownerEscape_or_capacity_or_largeJointFiber
          g hg h t q ht hq hmin hqzero z (H + 1) 3 J hcount with
      howner | hcapacity | hjoint
    · have hownerBound :=
        card_minimalSupportPrivateExternalHeavyOwnerEscapeVertices_le_selfHeavy_add_one
          g hg h t q ht hq hmin hqzero z
      change H + 1 <
        (minimalSupportPrivateExternalHeavyOwnerEscapeVertices
          g hg h t q ht hq hmin hqzero z).card at howner
      change (minimalSupportPrivateExternalHeavyOwnerEscapeVertices
          g hg h t q ht hq hmin hqzero z).card ≤ H + 1 at hownerBound
      omega
    · exact hcapacity
    · obtain ⟨e, _, heFiber⟩ := hjoint
      have howners :=
        card_minimalSupportPrivateJointExternalHeavyEscapeOwners_le_selfHeavy_or_capacity
          g hg h t hh q ht hq hmin hqzero z e
      rcases howners with hownerBound | hcapacity
      · have hcard := card_minimalSupportPrivateJointExternalHeavyEscapeOwners
          g hg h t q ht hq hmin hqzero z e
        change J < (minimalSupportPrivateJointExternalHeavyEscapeFiber
          g hg h t q ht hq hmin hqzero z e).card at heFiber
        change (minimalSupportPrivateJointExternalHeavyEscapeOwners
          g hg h t q ht hq hmin hqzero z e).card ≤ J at hownerBound
        omega
      · exact hcapacity

end MinModulus
