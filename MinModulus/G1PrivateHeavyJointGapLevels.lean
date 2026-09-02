/-
# Coefficient levels in the normalized joint gap fiber

After the three-coordinate capacity closure, the surviving directed gap is
the original common heavy coordinate `z`.  A witness coefficient outside its
exact omission set is bounded above by the number of omissions, hence by the
ambient coordinate count.  Heavy coefficients at `z` therefore occupy only
finitely many integer levels.

Large heavy-target families contain a repeated level.  Two distinct private
witnesses at that level agree at `z` and both omit `w`; validity forces their
next directed coefficient gap to occur away from both fixed coordinates.
-/
import MinModulus.G1PrivateHeavyJointGapCapacity

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The exact finset of coefficient-`-1` omissions of an arbitrary vector. -/
def witnessOmissionCoordinates (c : Fin m → ℤ) : Finset (Fin m) :=
  Finset.univ.filter (fun i ↦ c i = -1)

theorem witnessOmissionCoordinates_exact (c : Fin m → ℤ) :
    ExactOmissions c (witnessOmissionCoordinates c) := by
  intro i
  simp [witnessOmissionCoordinates]

theorem card_witnessOmissionCoordinates_le (c : Fin m → ℤ) :
    (witnessOmissionCoordinates c).card ≤ m := by
  simpa [witnessOmissionCoordinates] using
    Finset.card_le_univ (witnessOmissionCoordinates c)

/-- Every non-omitted witness coefficient is at most the total number of
omissions. -/
theorem witness_coeff_le_card_witnessOmissionCoordinates
    (g : Fin m → G) {h : G} {c : Fin m → ℤ}
    (hc : Witness g h c) {i : Fin m} (hi : c i ≠ -1) :
    c i ≤ ((witnessOmissionCoordinates c).card : ℤ) := by
  exact (witness_coeff_bounds_of_exactOmissions
    g hc (witnessOmissionCoordinates c)
      (witnessOmissionCoordinates_exact c)
      (by simpa [witnessOmissionCoordinates] using hi)).2

/-- Heavy coefficient values at the fixed joint heavy coordinate. -/
noncomputable def minimalSupportPrivateJointGapHeavyTargetLevels
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) : Finset ℤ := by
  classical
  exact (minimalSupportPrivateJointGapHeavyTargetVertices
    g hg h t hh q ht hq hmin hqzero z e delta w).image
      (fun b ↦ minimalSupportPrivateWitness g h hmin b.val z)

/-- Heavy targets at one fixed coefficient level. -/
noncomputable def minimalSupportPrivateJointGapHeavyTargetLevelFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ) :=
  (minimalSupportPrivateJointGapHeavyTargetVertices
    g hg h t hh q ht hq hmin hqzero z e delta w).filter
      (fun b ↦ minimalSupportPrivateWitness g h hmin b.val z = a)

/-- Once the selected gap is normalized to `z`, every realized heavy level
lies in the integer interval `[2,m+1]`. -/
theorem minimalSupportPrivateJointGapHeavyTargetLevels_subset_Icc
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (hfixed : delta = z) :
    minimalSupportPrivateJointGapHeavyTargetLevels
        g hg h t hh q ht hq hmin hqzero z e delta w ⊆
      Finset.Icc (2 : ℤ) (m + 1 : ℤ) := by
  classical
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  have hbSpec :=
    minimalSupportSelectedPrivateGapHeavyTargetVertices_spec
      g hg hh hmin
        (minimalSupportPrivateJointExternalHeavyEscapeOwners
          g hg h t q ht hq hmin hqzero z e) delta w hb
  have hcoordEq :
      minimalSupportPrivateWitness g h hmin b.val delta =
        minimalSupportPrivateWitness g h hmin b.val z :=
    congrArg (fun x ↦ minimalSupportPrivateWitness g h hmin b.val x) hfixed
  have hlower : 2 ≤ minimalSupportPrivateWitness g h hmin b.val z := by
    rw [← hcoordEq]
    exact hbSpec.2.2.2.1
  have hupper := witness_coeff_le_card_witnessOmissionCoordinates
    g (minimalSupportPrivateWitness_isWitness g h hmin b.val)
      (by omega : minimalSupportPrivateWitness g h hmin b.val z ≠ -1)
  have hcard := card_witnessOmissionCoordinates_le
    (minimalSupportPrivateWitness g h hmin b.val)
  have hcardCast :
      ((witnessOmissionCoordinates
        (minimalSupportPrivateWitness g h hmin b.val)).card : ℤ) ≤
        (m + 1 : ℤ) := by exact_mod_cast hcard
  exact Finset.mem_Icc.mpr ⟨hlower, hupper.trans hcardCast⟩

/-- There are at most `m` possible heavy coefficient levels `2,...,m+1`. -/
theorem card_minimalSupportPrivateJointGapHeavyTargetLevels_le
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (hfixed : delta = z) :
    (minimalSupportPrivateJointGapHeavyTargetLevels
      g hg h t hh q ht hq hmin hqzero z e delta w).card ≤ m := by
  have hsubset :=
    minimalSupportPrivateJointGapHeavyTargetLevels_subset_Icc
      g hg h t hh q ht hq hmin hqzero z e delta w hfixed
  have hcard := Finset.card_le_card hsubset
  rw [Int.card_Icc] at hcard
  omega

/-- If the normalized heavy-target family exceeds `m*r`, then more than `r`
targets share one coefficient level at the fixed heavy coordinate. -/
theorem exists_large_minimalSupportPrivateJointGapHeavyTargetLevelFiber
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (hfixed : delta = z) (r : ℕ)
    (hcount : m * r < (minimalSupportPrivateJointGapHeavyTargetVertices
      g hg h t hh q ht hq hmin hqzero z e delta w).card) :
    ∃ a ∈ minimalSupportPrivateJointGapHeavyTargetLevels
        g hg h t hh q ht hq hmin hqzero z e delta w,
      r < (minimalSupportPrivateJointGapHeavyTargetLevelFiber
        g hg h t hh q ht hq hmin hqzero z e delta w a).card := by
  classical
  let H := minimalSupportPrivateJointGapHeavyTargetVertices
    g hg h t hh q ht hq hmin hqzero z e delta w
  let level : ↥(minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e) → ℤ :=
    fun b ↦ minimalSupportPrivateWitness g h hmin b.val z
  let levels := minimalSupportPrivateJointGapHeavyTargetLevels
    g hg h t hh q ht hq hmin hqzero z e delta w
  have hlevels : levels.card ≤ m :=
    card_minimalSupportPrivateJointGapHeavyTargetLevels_le
      g hg h t hh q ht hq hmin hqzero z e delta w hfixed
  have hmul : levels.card * r < H.card :=
    lt_of_le_of_lt (Nat.mul_le_mul_right r hlevels) hcount
  have hmaps : ∀ b ∈ H, level b ∈ levels := by
    intro b hb
    exact Finset.mem_image.mpr ⟨b, hb, rfl⟩
  obtain ⟨a, ha, hfiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := level) hmaps hmul
  refine ⟨a, ha, ?_⟩
  simpa [level, H,
    minimalSupportPrivateJointGapHeavyTargetLevelFiber] using hfiber

/-- Two distinct private witnesses in one repeated heavy level agree at `z`
and both omit `w`; their next directed gap must therefore occur away from
both fixed coordinates. -/
theorem exists_fresh_gap_of_distinct_jointHeavyTarget_sameLevel
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    (h t : G) (hh : h + h = 0)
    (q : Fin (m + 1) → ℤ) (ht : t + t = h)
    (hq : Witness g t q)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hqzero : ∀ a ∈ B, q a = 0)
    (z e delta w : Fin (m + 1)) (a : ℤ)
    (b u : ↥(minimalSupportPrivateJointExternalHeavyEscapeOwners
      g hg h t q ht hq hmin hqzero z e))
    (hb : b ∈ minimalSupportPrivateJointGapHeavyTargetLevelFiber
      g hg h t hh q ht hq hmin hqzero z e delta w a)
    (hu : u ∈ minimalSupportPrivateJointGapHeavyTargetLevelFiber
      g hg h t hh q ht hq hmin hqzero z e delta w a)
    (hbu : b ≠ u) :
    ∃ i : Fin (m + 1),
      minimalSupportPrivateWitness g h hmin b.val i + 2 ≤
        minimalSupportPrivateWitness g h hmin u.val i ∧
      (i = u.val ∨ i ∉ B) ∧ i ≠ z ∧ i ≠ w := by
  have hbData := Finset.mem_filter.mp hb
  have huData := Finset.mem_filter.mp hu
  have howners : b.val ≠ u.val := by
    intro hval
    exact hbu (Subtype.ext hval)
  obtain ⟨i, hi, hiLocation⟩ :=
    exists_minimalSupportPrivateCoefficientGap_eq_targetOwner_or_external
      g hg h hmin b.val u.val howners
  have hbLevel := hbData.2
  have huLevel := huData.2
  have hbSpec :=
    minimalSupportSelectedPrivateGapHeavyTargetVertices_spec
      g hg hh hmin
        (minimalSupportPrivateJointExternalHeavyEscapeOwners
          g hg h t q ht hq hmin hqzero z e) delta w hbData.1
  have huSpec :=
    minimalSupportSelectedPrivateGapHeavyTargetVertices_spec
      g hg hh hmin
        (minimalSupportPrivateJointExternalHeavyEscapeOwners
          g hg h t q ht hq hmin hqzero z e) delta w huData.1
  have hiz : i ≠ z := by
    intro hiz
    rw [hiz, hbLevel, huLevel] at hi
    omega
  have hiw : i ≠ w := by
    intro hiw
    rw [hiw, hbSpec.2.2.2.2, huSpec.2.2.2.2] at hi
    omega
  exact ⟨i, hi, hiLocation, hiz, hiw⟩

end MinModulus
