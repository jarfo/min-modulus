/-
# Three-coordinate capacity from a joint gap fiber

Specialize the fixed-gap source/target split to owners lifted from one joint
external heavy/escape fiber.  Every lifted witness is coefficient-heavy at
the fixed external heavy coordinate `z`.

A source which omits the gap coordinate cannot therefore have `gap = z`.
Together with the common omission this exposes three distinct coordinates
outside the deletion set and forces an immediate `|B| + 3` ambient-capacity
bound.  Likewise, a gap-heavy target has the same consequence unless the gap
coordinate is exactly `z`.
-/
import MinModulus.G1PrivateHeavyGapSourceTargetSplit

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Three pairwise distinct coordinates outside a finite coordinate set
consume three units of ambient capacity. -/
theorem card_add_three_le_of_three_external
    {B : Finset (Fin m)} {a b c : Fin m}
    (haB : a ∉ B) (hbB : b ∉ B) (hcB : c ∉ B)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    B.card + 3 ≤ m := by
  classical
  have hcInsert : c ∉ B := hcB
  have hbInsert : b ∉ insert c B := by simp [hbB, hbc]
  have haInsert : a ∉ insert b (insert c B) := by
    simp [haB, hab, hac]
  have hcard : (insert a (insert b (insert c B))).card = B.card + 3 := by
    rw [Finset.card_insert_of_notMem haInsert,
      Finset.card_insert_of_notMem hbInsert,
      Finset.card_insert_of_notMem hcInsert]
  rw [← hcard]
  simpa using Finset.card_le_univ (insert a (insert b (insert c B)))

/-- The selected pair fiber with fixed gap and omission over the owner image
of one joint heavy/escape fiber. -/
noncomputable def minimalSupportPrivateJointGapOmissionFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) :=
  minimalSupportSelectedPrivateExternalGapOmissionFiber
    g hg hh hmin
      (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e) delta w

/-- Endpoint owners of the specialized joint gap/omission fiber. -/
noncomputable def minimalSupportPrivateJointGapOmissionVertices
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) :=
  minimalSupportSelectedPrivateExternalGapOmissionVertices
    g hg hh hmin
      (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e) delta w

/-- Specialized sources omitting both the gap and common omission. -/
noncomputable def minimalSupportPrivateJointGapSourceOmissionVertices
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) :=
  minimalSupportSelectedPrivateGapSourceOmissionVertices
    g hg hh hmin
      (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e) delta w

/-- Specialized targets heavy at the gap and omitting the common omission. -/
noncomputable def minimalSupportPrivateJointGapHeavyTargetVertices
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) :=
  minimalSupportSelectedPrivateGapHeavyTargetVertices
    g hg hh hmin
      (minimalSupportPrivateJointExternalHeavyEscapeOwners
        g hg h t q ht hq hmin hqzero z e) delta w

/-- Membership in a joint fiber makes the lifted private witness heavy at
its fixed external heavy coordinate. -/
theorem minimalSupportPrivateJointOwnerLift_heavy_at_fixed
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e : Fin (m + 1))
    (b : ↥(minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e)) :
    z ∉ B ∧
      2 ≤ minimalSupportPrivateWitness g h hmin b.val z := by
  let b' := minimalSupportPrivateJointOwnerLift
    g hg h t q ht hq hmin hqzero z e b
  have hbJoint := Finset.mem_filter.mp b'.property
  have hbDouble := Finset.mem_filter.mp hbJoint.1
  have hbExternal :=
    (mem_minimalSupportPrivateExternalHeavyFiber_iff
      g h hmin z b'.val).mp hbDouble.1
  have hzB :=
    (mem_minimalSupportPrivateExternalHeavyVertices_iff
      g h hmin b'.val).mp hbExternal.1
  rw [hbExternal.2] at hzB
  have hbHeavy := minimalSupportPrivateHeavyCoordinate_spec g h hmin b'.val
  rw [hbExternal.2] at hbHeavy
  have hbval : b'.val.val = b.val := by simp [b']
  rw [hbval] at hbHeavy
  exact ⟨hzB, hbHeavy⟩

/-- One joint-fiber source omitting the fixed gap already exposes three
distinct external coordinates: the original heavy coordinate, the gap, and
the common omission. -/
theorem minimalSupportPrivateJointGapSourceOmission_card_add_three_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1))
    {b : ↥(minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e)}
    (hb : b ∈ minimalSupportPrivateJointGapSourceOmissionVertices
      g hg h t hh q ht hq hmin hqzero z e delta w) :
    B.card + 3 ≤ m + 1 := by
  have hbSource :=
    minimalSupportSelectedPrivateGapSourceOmissionVertices_spec
      g hg hh hmin
        (minimalSupportPrivateJointExternalHeavyEscapeOwners
          g hg h t q ht hq hmin hqzero z e) delta w hb
  have hbHeavy := minimalSupportPrivateJointOwnerLift_heavy_at_fixed
    g hg h t q ht hq hmin hqzero z e b
  have hzDelta : z ≠ delta := by
    intro heq
    have hdeltaHeavy :
        2 ≤ minimalSupportPrivateWitness g h hmin b.val delta := by
      rw [← heq]
      exact hbHeavy.2
    rw [hbSource.2.2.2.1] at hdeltaHeavy
    omega
  have hzW : z ≠ w := by
    intro heq
    have hwHeavy :
        2 ≤ minimalSupportPrivateWitness g h hmin b.val w := by
      rw [← heq]
      exact hbHeavy.2
    rw [hbSource.2.2.2.2] at hwHeavy
    omega
  exact card_add_three_le_of_three_external
    hbHeavy.1 hbSource.1 hbSource.2.1
      hzDelta hzW (Ne.symm hbSource.2.2.1)

/-- A joint-fiber target heavy at the selected gap either uses the original
common heavy coordinate or also exposes three distinct external coordinates. -/
theorem minimalSupportPrivateJointGapHeavyTarget_eq_fixed_or_card_add_three_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1))
    {b : ↥(minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e)}
    (hb : b ∈ minimalSupportPrivateJointGapHeavyTargetVertices
      g hg h t hh q ht hq hmin hqzero z e delta w) :
    delta = z ∨ B.card + 3 ≤ m + 1 := by
  by_cases hdelta : delta = z
  · exact Or.inl hdelta
  · right
    have hbTarget :=
      minimalSupportSelectedPrivateGapHeavyTargetVertices_spec
        g hg hh hmin
          (minimalSupportPrivateJointExternalHeavyEscapeOwners
            g hg h t q ht hq hmin hqzero z e) delta w hb
    have hbHeavy := minimalSupportPrivateJointOwnerLift_heavy_at_fixed
      g hg h t q ht hq hmin hqzero z e b
    have hzW : z ≠ w := by
      intro heq
      have hwHeavy :
          2 ≤ minimalSupportPrivateWitness g h hmin b.val w := by
        rw [← heq]
        exact hbHeavy.2
      rw [hbTarget.2.2.2.2] at hwHeavy
      omega
    exact card_add_three_le_of_three_external
      hbHeavy.1 hbTarget.1 hbTarget.2.1
        (Ne.symm hdelta) hzW (Ne.symm hbTarget.2.2.1)

/-- In the joint specialization, a dense fixed `(gap, omission)` fiber
either forces the three-coordinate capacity bound or produces many targets
whose gap is exactly the original common heavy coordinate. -/
theorem minimalSupportPrivateJointGap_capacity_three_or_manyHeavyAtFixed
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (A C : ℕ)
    (hcount : (A + C) *
        (minimalSupportPrivateJointGapOmissionVertices
          g hg h t hh q ht hq hmin hqzero z e delta w).card <
      (minimalSupportPrivateJointGapOmissionFiber
        g hg h t hh q ht hq hmin hqzero z e delta w).card) :
    B.card + 3 ≤ m + 1 ∨
      delta = z ∧ C <
        (minimalSupportPrivateJointGapHeavyTargetVertices
          g hg h t hh q ht hq hmin hqzero z e delta w).card := by
  have hsplit :=
    minimalSupportSelectedPrivateGap_manySourceOmissions_or_manyHeavyTargets
      g hg hh hmin
        (minimalSupportPrivateJointExternalHeavyEscapeOwners
          g hg h t q ht hq hmin hqzero z e) delta w A C hcount
  rcases hsplit with hsource | htarget
  · left
    have hnonempty :
        (minimalSupportPrivateJointGapSourceOmissionVertices
          g hg h t hh q ht hq hmin hqzero z e delta w).Nonempty :=
      Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le A) hsource)
    obtain ⟨b, hb⟩ := hnonempty
    exact minimalSupportPrivateJointGapSourceOmission_card_add_three_le
      g hg h t hh q ht hq hmin hqzero z e delta w hb
  · have hnonempty :
        (minimalSupportPrivateJointGapHeavyTargetVertices
          g hg h t hh q ht hq hmin hqzero z e delta w).Nonempty :=
      Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le C) htarget)
    obtain ⟨b, hb⟩ := hnonempty
    rcases
        minimalSupportPrivateJointGapHeavyTarget_eq_fixed_or_card_add_three_le
          g hg h t hh q ht hq hmin hqzero z e delta w hb with
      hfixed | hcapacity
    · exact Or.inr ⟨hfixed, htarget⟩
    · exact Or.inl hcapacity

end MinModulus
