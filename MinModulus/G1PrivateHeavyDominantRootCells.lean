/-
# Dominant-root cells of the private-heavy cycle

Non-dominant deterministic cells pay for external support by strict support
growth.  The remaining cells canonicalize to the dominant root itself and
have depth zero.  Their complete incoming avoiding profiles still expose a
stronger fact: every occurrence supplies a distinct predecessor/source zero
outside the root support, apart from the one possible anchor source.

Thus all root-cell occurrences together, across both raw orientations and
all labels, are bounded by the root's binary padding depth.  This treats the
root fiber jointly rather than paying one dominant weight for each of its at
most four cells.
-/
import MinModulus.G1PrivateHeavyDominantCycleSupportEscape

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Retained cycle indices whose deterministic cell canonicalizes to one
fixed collision. -/
noncomputable def minimalSupportPrivateShiftCycleDominantRootIndices
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h) := by
  classical
  exact
    (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
      g hg hh hno hmin a d).attach.filter fun i ↦
        minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
          g hg hh hno hmin a d
            (minimalSupportPrivateShiftCycleLabelProfileAt
              g hg hh hno hmin a d i) = r

/-- Retained cycle indices whose deterministic cell does not canonicalize to
the fixed root. -/
noncomputable def minimalSupportPrivateShiftCycleNonDominantIndices
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h) := by
  classical
  exact
    (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
      g hg hh hno hmin a d).attach.filter fun i ↦
        minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
          g hg hh hno hmin a d
            (minimalSupportPrivateShiftCycleLabelProfileAt
              g hg hh hno hmin a d i) ≠ r

/-- Root and non-root occurrences partition the complete retained cycle-index
family. -/
theorem card_dominantRootIndices_add_nonDominantIndices
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h) :
    (minimalSupportPrivateShiftCycleDominantRootIndices
        g hg hh hno hmin a d r).card +
      (minimalSupportPrivateShiftCycleNonDominantIndices
        g hg hh hno hmin a d r).card =
      (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card := by
  classical
  let R := minimalSupportPrivateShiftCycleLabelledLightProfileIndices
    g hg hh hno hmin a d
  let canAt : ↥R → ReducedSubsetSumCollision g h := fun i ↦
    minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision
      g hg hh hno hmin a d
        (minimalSupportPrivateShiftCycleLabelProfileAt
          g hg hh hno hmin a d i)
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := R.attach) (p := fun i ↦ canAt i = r)
  simpa [R, canAt, minimalSupportPrivateShiftCycleDominantRootIndices,
    minimalSupportPrivateShiftCycleNonDominantIndices] using hpartition

omit [DecidableEq G] in
/-- The raw collision of any active deterministic cell has exactly the cell's
complete incoming avoiding coefficient profile. -/
theorem labelProfileCellRawCollision_coeffs
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)) :
    subsetCollisionCoeffs
        (minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
          g hg hh hno hmin a d p).val.1
        (minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
          g hg hh hno hmin a d p).val.2 = p.2.val := by
  simpa [minimalSupportPrivateShiftCycleLabelProfileCellRawCollision,
    incomingAvoidingLightProfileRawCollision] using
      reducedCollisionOfTailLightWitness_coeffs g
        (incomingAvoidingLightProfile_isWitness g hno hmin a d p.2)
        (incomingAvoidingLightProfile_tailLight g hno hmin a d p.2)

/-- A cell over the dominant root has one of the two raw orientations. -/
theorem dominantRootLabelProfileCell_rawOrientation
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (r : ReducedSubsetSumCollision g h)
    {p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)}
    (hp : p ∈ minimalSupportPrivateShiftCycleLabelProfileCellCanonicalFiber
      g hg hh hno hmin a d r) :
    minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
          g hg hh hno hmin a d p = r ∨
      minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
          g hg hh hno hmin a d p =
        reducedSubsetSumCollisionSwapEquiv hh r := by
  classical
  have hp' := Finset.mem_filter.mp hp
  exact eq_or_eq_swap_of_canonicalizeReducedCollision_eq hh _ r hp'.2

/-- For a root cell, a tail omission label lies on the negative side in the
raw orientation: on `r.val.2` in the root orientation and on `r.val.1` in the
swapped orientation.  The anchor label is retained as the only separate
case. -/
theorem dominantRootLabelProfileCell_label_zero_or_mem_orientedSide
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (r : ReducedSubsetSumCollision g h)
    {p : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d)}
    (hp : p ∈ minimalSupportPrivateShiftCycleLabelProfileCellCanonicalFiber
      g hg hh hno hmin a d r) :
    p.1 = 0 ∨
      ∃ k : Fin m, p.1 = k.succ ∧
        ((minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
              g hg hh hno hmin a d p = r ∧ k ∈ r.val.2) ∨
          (minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
              g hg hh hno hmin a d p =
                reducedSubsetSumCollisionSwapEquiv hh r ∧ k ∈ r.val.1)) := by
  classical
  have hpC := (Finset.mem_filter.mp hp).1
  have homit := active_labelProfileCell_omits
    g hg hh hno hmin a d p hpC
  rcases p.1.eq_zero_or_eq_succ with hzero | ⟨k, hk⟩
  · exact Or.inl hzero
  · right
    refine ⟨k, hk, ?_⟩
    let raw := minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
      g hg hh hno hmin a d p
    have hcoeff := labelProfileCellRawCollision_coeffs
      g hg hh hno hmin a d p
    have hneg : subsetCollisionCoeffs raw.val.1 raw.val.2 k.succ = -1 := by
      rw [hcoeff]
      simpa [hk] using homit
    have hkRaw : k ∈ raw.val.2 :=
      (Finset.mem_sdiff.mp
        ((subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
          raw.val.1 raw.val.2 k).mp hneg)).1
    rcases dominantRootLabelProfileCell_rawOrientation
        g hg hh hno hmin a d r hp with hraw | hraw
    · left
      exact ⟨hraw, by simpa [raw, hraw] using hkRaw⟩
    · right
      refine ⟨hraw, ?_⟩
      simpa [raw, hraw, reducedSubsetSumCollisionSwapEquiv] using hkRaw

/-- A root index's incoming avoiding profile vanishes at its predecessor.
Every non-anchor predecessor is a tail coordinate outside the root support,
independently of which raw orientation represents the root. -/
theorem dominantRootIndex_source_zero_and_tailOutsideSupport
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ)
    (r : ReducedSubsetSumCollision g h)
    {i : ↥(minimalSupportPrivateShiftCycleLabelledLightProfileIndices
      g hg hh hno hmin a d)}
    (hi : i ∈ minimalSupportPrivateShiftCycleDominantRootIndices
      g hg hh hno hmin a d r) :
    let source : Fin (m + 1) :=
      minimalSupportPrivateShiftCycleVertex g hno hmin a
        ((finRotate d).symm i.val)
    (minimalSupportPrivateShiftCycleLabelProfileAt
      g hg hh hno hmin a d i).2.val source = 0 ∧
      ∀ k : Fin m, source = k.succ →
        k ∉ reducedCollisionSupport r := by
  classical
  let source : Fin (m + 1) :=
    minimalSupportPrivateShiftCycleVertex g hno hmin a
      ((finRotate d).symm i.val)
  let p := minimalSupportPrivateShiftCycleLabelProfileAt
    g hg hh hno hmin a d i
  let raw := minimalSupportPrivateShiftCycleLabelProfileCellRawCollision
    g hg hh hno hmin a d p
  have hzero : p.2.val source = 0 := by
    change minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a i.val source = 0
    simpa [minimalSupportPrivateShiftCycleIncomingAvoidingWitness, source]
      using minimalSupportAvoidingWitness_eq_zero g hno
        (minimalSupportPrivateShiftCycleVertex g hno hmin a
          ((finRotate d).symm i.val))
  refine ⟨hzero, ?_⟩
  intro k hsource
  have hiRoot := (Finset.mem_filter.mp hi).2
  have horient : raw = r ∨ raw = reducedSubsetSumCollisionSwapEquiv hh r :=
    eq_or_eq_swap_of_canonicalizeReducedCollision_eq hh raw r (by
      simpa [p, raw,
        minimalSupportPrivateShiftCycleLabelProfileCellCanonicalCollision]
        using hiRoot)
  have hsupport : raw.val.1 ∪ raw.val.2 =
      r.val.1 ∪ r.val.2 := by
    rcases horient with hraw | hraw
    · simp [hraw]
    · simp [hraw, reducedSubsetSumCollisionSwapEquiv,
        Finset.union_comm]
  have hcoeff := labelProfileCellRawCollision_coeffs
    g hg hh hno hmin a d p
  have hrawZero : subsetCollisionCoeffs raw.val.1 raw.val.2 k.succ = 0 := by
    rw [hcoeff, ← hsource]
    exact hzero
  intro hkRoot
  have hkRaw : k ∈ raw.val.1 ∪ raw.val.2 := by
    rw [hsupport]
    simpa [reducedCollisionSupport] using hkRoot
  have hdisj := Finset.disjoint_left.mp raw.property.1
  rcases Finset.mem_union.mp hkRaw with hkA | hkB
  · have hkBn : k ∉ raw.val.2 := fun hkB ↦ hdisj hkA hkB
    simp [subsetCollisionCoeffs, hkA, hkBn] at hrawZero
  · have hkAn : k ∉ raw.val.1 := fun hkA ↦ hdisj hkA hkB
    simp [subsetCollisionCoeffs, hkAn, hkB] at hrawZero

/-- All dominant-root cycle occurrences share the root's padding capacity.
After losing the possible anchor predecessor, their distinct source zeros fit
outside the root support. -/
theorem card_dominantRootIndices_sub_one_le_paddingDepth
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : ReducedSubsetSumCollision g h) :
    (minimalSupportPrivateShiftCycleDominantRootIndices
        g hg hh hno hmin a d r).card - 1 ≤
      m - (reducedCollisionSupport r).card := by
  classical
  let F := minimalSupportPrivateShiftCycleDominantRootIndices
    g hg hh hno hmin a d r
  let source :
      ↥(minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d) → Fin (m + 1) := fun i ↦
    minimalSupportPrivateShiftCycleVertex g hno hmin a
      ((finRotate d).symm i.val)
  let S := F.image source
  let T := reducedCollisionSupport r
  let TS := T.image Fin.succ
  let U := (Finset.univ : Finset (Fin (m + 1))).erase 0
  have hsourceInjective : Function.Injective source := by
    intro i j hij
    apply Subtype.ext
    apply (finRotate d).symm.injective
    apply minimalSupportPrivateShiftCycleVertex_injective
      g hno hmin a hcycle
    simpa [source] using hij
  have hScard : S.card = F.card :=
    Finset.card_image_of_injective F hsourceInjective
  have hdisjoint : Disjoint (S.erase 0) TS := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxT
    obtain ⟨i, hiF, hix⟩ := Finset.mem_image.mp
      (Finset.mem_of_mem_erase hxS)
    obtain ⟨k, hkT, hkx⟩ := Finset.mem_image.mp hxT
    have hout :=
      (dominantRootIndex_source_zero_and_tailOutsideSupport
        g hg hh hno hmin a d r hiF).2 k
    apply hout
    · exact hix.trans hkx.symm
    · exact hkT
  have hSsubset : S.erase 0 ⊆ U := by
    intro x hx
    exact Finset.mem_erase.mpr
      ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ x⟩
  have hTSsubset : TS ⊆ U := by
    intro x hx
    obtain ⟨k, _hk, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨Fin.succ_ne_zero k, Finset.mem_univ _⟩
  have hTScard : TS.card = T.card :=
    Finset.card_image_of_injective T (Fin.succ_injective m)
  have hcapacity : (S.erase 0).card + T.card ≤ m := by
    have hcard := Finset.card_le_card
      (Finset.union_subset hSsubset hTSsubset)
    rw [Finset.card_union_of_disjoint hdisjoint, hTScard] at hcard
    simpa [U] using hcard
  have hsourceCard : F.card - 1 ≤ (S.erase 0).card := by
    by_cases h0 : 0 ∈ S
    · have herase := Finset.card_erase_add_one h0
      omega
    · rw [(Finset.erase_eq_self.mpr h0), hScard]
      exact Nat.sub_le _ _
  change F.card - 1 ≤ m - T.card
  omega

/-- Exponential form of the joint root-index padding bound. -/
theorem pow_card_dominantRootIndices_sub_one_le_weight
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : ReducedSubsetSumCollision g h) :
    2 ^ ((minimalSupportPrivateShiftCycleDominantRootIndices
        g hg hh hno hmin a d r).card - 1) ≤
      reducedCollisionWeight (m := m) r := by
  have hdepth := card_dominantRootIndices_sub_one_le_paddingDepth
    g hg hh hno hmin a hcycle r
  exact Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hdepth

/-- Non-root retained indices are bounded by the sum of the source-zero powers
of their non-dominant deterministic cells. -/
theorem card_nonDominantIndices_le_sum_cellFiberPowers
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : ReducedSubsetSumCollision g h) :
    (minimalSupportPrivateShiftCycleNonDominantIndices
        g hg hh hno hmin a d r).card ≤
      (minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
        g hg hh hno hmin a d r).sum (fun p ↦
          2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
            g hno hmin a d p.2.val).card - 1)) := by
  classical
  let R := minimalSupportPrivateShiftCycleLabelledLightProfileIndices
    g hg hh hno hmin a d
  let N := minimalSupportPrivateShiftCycleNonDominantIndices
    g hg hh hno hmin a d r
  let C₀ := minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
    g hg hh hno hmin a d r
  let labelProfile := minimalSupportPrivateShiftCycleLabelProfileAt
    g hg hh hno hmin a d
  let cell := minimalSupportPrivateShiftCycleLabelProfileCell
    g hg hh hno hmin a d
  let power : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d p.2.val).card - 1)
  have himage : N.image labelProfile ⊆ C₀ := by
    intro p hp
    obtain ⟨i, hiN, rfl⟩ := Finset.mem_image.mp hp
    have hiN' := Finset.mem_filter.mp hiN
    apply Finset.mem_filter.mpr
    refine ⟨?_, hiN'.2⟩
    apply
      (mem_minimalSupportPrivateShiftCycleLabelProfileCells_iff
        g hg hh hno hmin a d _).mpr
    exact ⟨i, rfl⟩
  have hfiber : ∀ p ∈ N.image labelProfile,
      (N.filter fun i ↦ labelProfile i = p).card ≤ (cell p).card := by
    intro p _hp
    apply Finset.card_le_card
    intro i hi
    have hi' := Finset.mem_filter.mp hi
    apply
      (mem_minimalSupportPrivateShiftCycleLabelProfileCell_iff
        g hg hh hno hmin a d p i).mpr
    exact hi'.2
  have hcell : ∀ p ∈ C₀, (cell p).card ≤ power p := by
    intro p hp
    exact card_labelProfileCell_le_pow_profileFiber_sub_one
      g hg hh hno hmin a d p (Finset.mem_filter.mp hp).1
  change N.card ≤ C₀.sum power
  calc
    N.card = ∑ p ∈ N.image labelProfile,
        (N.filter fun i ↦ labelProfile i = p).card :=
      Finset.card_eq_sum_card_image labelProfile N
    _ ≤ ∑ p ∈ N.image labelProfile, (cell p).card := by
      exact Finset.sum_le_sum fun p hp ↦ hfiber p hp
    _ ≤ C₀.sum (fun p ↦ (cell p).card) :=
      Finset.sum_le_sum_of_subset himage
    _ ≤ C₀.sum power := by
      exact Finset.sum_le_sum fun p hp ↦ hcell p hp

/-- Joint root/non-root cycle bound.  Root occurrences cost only the root
padding depth, while all non-root occurrences retain the strict four-weight
budget. -/
theorem cycleLength_lt_four_mul_weight_add_paddingDepth_add_two
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    (hd : d ≤
      (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card + 1) :
    d < 4 * reducedCollisionWeight (m := m) r +
      (m - (reducedCollisionSupport r).card) + 2 := by
  let F := minimalSupportPrivateShiftCycleDominantRootIndices
    g hg hh hno hmin a d r
  let N := minimalSupportPrivateShiftCycleNonDominantIndices
    g hg hh hno hmin a d r
  let C₀ := minimalSupportPrivateShiftCycleNonDominantLabelProfileCells
    g hg hh hno hmin a d r
  let power : Fin (m + 1) ×
      ↥(minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles
        g hno hmin a d) → ℕ := fun p ↦
    2 ^ ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d p.2.val).card - 1)
  have hpartition := card_dominantRootIndices_add_nonDominantIndices
    g hg hh hno hmin a d r
  have hroot := card_dominantRootIndices_sub_one_le_paddingDepth
    g hg hh hno hmin a hcycle r
  have hnon := card_nonDominantIndices_le_sum_cellFiberPowers
    g hg hh hno hmin a d r
  have hpower :=
    sum_nonDominantActiveLabelProfileCellFiberPowers_lt_four_mul_weight
      g hg hh hh0 hthree hno hmin a hcycle r hr hmajor
  change F.card + N.card =
      (minimalSupportPrivateShiftCycleLabelledLightProfileIndices
        g hg hh hno hmin a d).card at hpartition
  change F.card - 1 ≤ m - (reducedCollisionSupport r).card at hroot
  change N.card ≤ C₀.sum power at hnon
  change C₀.sum power < 4 * reducedCollisionWeight (m := m) r at hpower
  omega

/-- Critical private-heavy dominant residual with both the non-root weighted
support surplus and the joint root-index padding bound. -/
noncomputable def IsCriticalPrivateHeavyDominantRootControlledCycle
    {n s q : ℕ}
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q))
    (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B) (d : ℕ)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) : Prop :=
  IsCriticalPrivateHeavyDominantCycleSupportEscape
      g hg hno hmin a d r ∧
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    (minimalSupportPrivateShiftCycleDominantRootIndices
        g hg hh hno hmin a d r).card - 1 ≤
      n - (reducedCollisionSupport r).card ∧
    d < 4 * reducedCollisionWeight (m := n) r +
      (n - (reducedCollisionSupport r).card) + 2

/-- Critical endpoint after jointly controlling both sides of the cycle-cell
partition.  Non-root cells pay weighted external-support surplus; all root
occurrences together fit in the root padding depth. -/
theorem critical_privateShiftCycle_cross_or_profiles_or_dominantRootControl
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1))
    (hno : ¬ ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      WitnessExactOmissionTriangle g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessThreeDistinctOmissions g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalPrivateHeavyDominantRootControlledCycle
          g hg hno hmin a d r := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hh0 : h ≠ 0 := by
    simpa [h] using half_ne_zero hN hM
  by_cases hthree : WitnessThreeDistinctOmissions g h
  · exact Or.inr (Or.inr (Or.inl hthree))
  rcases
      critical_privateShiftCycle_cross_or_profiles_or_labelledLightProfileIndices_add_one
        hq g hg hno hmin a hcycle hB with
    hcycleCross | htriangle | hthree' | hpure | hlabelled
  · exact Or.inl hcycleCross
  · exact Or.inr (Or.inl htriangle)
  · exact False.elim (hthree hthree')
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpure)))
  rcases critical_privateShiftCycle_cross_or_profiles_or_dominantSupportEscape
      hn hq g hg hcritical hno hmin a hcycle hB with
    hcross | htriangle | hthree' | hpure | hdominant
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htriangle)
  · exact False.elim (hthree hthree')
  · exact Or.inr (Or.inr (Or.inr (Or.inl hpure)))
  · right; right; right; right
    obtain ⟨r, hr, hres⟩ := hdominant
    refine ⟨r, hr, ?_⟩
    simp only [IsCriticalPrivateHeavyDominantRootControlledCycle]
    refine ⟨hres, ?_, ?_⟩
    · have hroot := card_dominantRootIndices_sub_one_le_paddingDepth
        g hg hh hno hmin a hcycle r
      simpa [h, hh] using hroot
    · have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
        simpa [h, hh, criticalCanonicalReducedCollisions] using hr
      have hcoupling : IsCriticalPrivateHeavyDominantCycleCoupling
          g hg hno hmin a d r := hres.1
      have hcoupling' := hcoupling
      simp only [IsCriticalPrivateHeavyDominantCycleCoupling] at hcoupling'
      have hmajor : (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := n)) <
        2 * reducedCollisionWeight (m := n) r := by
        simpa [h, hh, criticalCanonicalReducedCollisions] using
          hcoupling'.2.2.2.2.1
      have hsharp :=
        cycleLength_lt_four_mul_weight_add_paddingDepth_add_two
          g hg hh hh0 hthree hno hmin a hcycle r hr' hmajor hlabelled
      simpa [h, hh] using hsharp

end MinModulus
