/-
# Clean ordered slices from positive-tail-meeting signatures

The avoiding/meeting partition isolates negative-tail coordinates covered by
signatures that meet the positive tail.  A subset in such a signature layer
automatically omits a positive-tail coordinate.  Every escape signature also
meets the negative tail, so the same subset omits a negative-tail coordinate.
Consequently ordered first-present slices built only from meeting signatures
are disjoint from both upper faces and require no contamination payment.

With no private half-cube markers to exclude, slice `i` fixes only the first
`i+1` ordered meeting-covered coordinates.  Its floor is therefore
`2^(padding-(i+1))`.
-/
import MinModulus.G1SignatureOrderedSlices

namespace MinModulus

open Finset

variable {m : ℕ}

/-- Geometric surplus supplied by `t` clean meeting-signature slices. -/
def orderedMeetingTailSurplus (padding t : ℕ) : ℕ :=
  ∑ i : Fin t, 2 ^ (padding - (i.1 + 1))

/-- Union of all meeting-signature slices at one first-present marker. -/
noncomputable def coveredMeetingOrderedTailSliceAt
    (S : Finset (Finset (Fin m))) (Y : Finset (Fin m))
    (i : Fin Y.card) : Finset (Finset (Fin m)) :=
  coveredSingletonTailSliceAt S (orderedTailPrefix Y i)
    (orderedTailCoordinate Y i)

/-- Complete clean ordered slice family over the meeting-covered tail. -/
noncomputable def coveredMeetingOrderedTailSlices
    (S : Finset (Finset (Fin m))) (Y : Finset (Fin m)) :
    Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.biUnion (coveredMeetingOrderedTailSliceAt S Y)

/-- If every coordinate of `Y` is covered by an omission from `B`, then every
sub-finset of `Y` is covered by its own signature differences. -/
theorem biUnion_sdiff_eq_self_of_subset_of_subset_biUnion_sdiff
    (S : Finset (Finset (Fin m))) (B Y T : Finset (Fin m))
    (hTY : T ⊆ Y)
    (hYcover : Y ⊆ S.biUnion (fun C ↦ B \ C)) :
    S.biUnion (fun C ↦ T \ C) = T := by
  classical
  apply Finset.Subset.antisymm
  · intro l hl
    rcases Finset.mem_biUnion.mp hl with ⟨C, hC, hlTC⟩
    exact (Finset.mem_sdiff.mp hlTC).1
  · intro l hlT
    have hlCover : l ∈ S.biUnion (fun C ↦ B \ C) := hYcover (hTY hlT)
    rcases Finset.mem_biUnion.mp hlCover with ⟨C, hC, hlBC⟩
    exact Finset.mem_biUnion.mpr
      ⟨C, hC, Finset.mem_sdiff.mpr
        ⟨hlT, (Finset.mem_sdiff.mp hlBC).2⟩⟩

/-- Each clean ordered meeting slice has the `i+1` marker floor. -/
theorem pow_padding_sub_meetingIndex_le_card_coveredMeetingOrderedAt
    (R B Y : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (i : Fin Y.card)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hYcover : Y ⊆ S.biUnion (fun C ↦ B \ C)) :
    2 ^ (m - R.card - (i.1 + 1)) ≤
      (coveredMeetingOrderedTailSliceAt S Y i).card := by
  classical
  let T := orderedTailPrefix Y i
  let l := orderedTailCoordinate Y i
  have hTY : T ⊆ Y := orderedTailPrefix_subset Y i
  have hcoverT : S.biUnion (fun C ↦ T \ C) = T :=
    biUnion_sdiff_eq_self_of_subset_of_subset_biUnion_sdiff
      S B Y T hTY hYcover
  have hlT : l ∈ T := orderedTailCoordinate_mem_prefix Y i
  have hfloor := pow_padding_sub_tailCard_le_card_coveredAt
    R T S hcards hcoverT hlT
  simpa [T, l, coveredMeetingOrderedTailSliceAt,
    card_orderedTailPrefix] using hfloor

/-- Distinct first-present meeting slices are disjoint. -/
theorem coveredMeetingOrderedTailSliceAt_disjoint
    (S : Finset (Finset (Fin m))) (Y : Finset (Fin m))
    {i u : Fin Y.card} (hiu : i ≠ u) :
    Disjoint (coveredMeetingOrderedTailSliceAt S Y i)
      (coveredMeetingOrderedTailSliceAt S Y u) := by
  classical
  rw [Finset.disjoint_left]
  intro U hUi hUu
  have hiInter := inter_tail_eq_singleton_of_mem_coveredAt
    S (orderedTailPrefix Y i) (orderedTailCoordinate Y i) hUi
  have huInter := inter_tail_eq_singleton_of_mem_coveredAt
    S (orderedTailPrefix Y u) (orderedTailCoordinate Y u) hUu
  rcases lt_or_gt_of_ne hiu with hiu' | hui'
  · have hiU : orderedTailCoordinate Y i ∈ U := by
      have hi : orderedTailCoordinate Y i ∈ U ∩ orderedTailPrefix Y i := by
        rw [hiInter]
        simp
      exact (Finset.mem_inter.mp hi).1
    have hiSingleton : orderedTailCoordinate Y i ∈
        ({orderedTailCoordinate Y u} : Finset (Fin m)) := by
      rw [← huInter]
      exact Finset.mem_inter.mpr
        ⟨hiU, orderedTailCoordinate_mem_laterPrefix Y hiu'⟩
    have hcoord : orderedTailCoordinate Y i = orderedTailCoordinate Y u := by
      simpa using hiSingleton
    exact hiu ((Y.orderEmbOfFin rfl).injective hcoord)
  · have huU : orderedTailCoordinate Y u ∈ U := by
      have hu : orderedTailCoordinate Y u ∈ U ∩ orderedTailPrefix Y u := by
        rw [huInter]
        simp
      exact (Finset.mem_inter.mp hu).1
    have huSingleton : orderedTailCoordinate Y u ∈
        ({orderedTailCoordinate Y i} : Finset (Fin m)) := by
      rw [← hiInter]
      exact Finset.mem_inter.mpr
        ⟨huU, orderedTailCoordinate_mem_laterPrefix Y hui'⟩
    have hcoord : orderedTailCoordinate Y u = orderedTailCoordinate Y i := by
      simpa using huSingleton
    exact hiu ((Y.orderEmbOfFin rfl).injective hcoord).symm

/-- The complete clean slice family has the ordered meeting-tail geometric
floor. -/
theorem orderedMeetingTailSurplus_le_card_coveredMeetingOrderedSlices
    (R B Y : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hYcover : Y ⊆ S.biUnion (fun C ↦ B \ C)) :
    orderedMeetingTailSurplus (m - R.card) Y.card ≤
      (coveredMeetingOrderedTailSlices S Y).card := by
  classical
  have hpairwise :
      ((Finset.univ : Finset (Fin Y.card)) : Set (Fin Y.card)).PairwiseDisjoint
        (coveredMeetingOrderedTailSliceAt S Y) := by
    intro i hi u hu hiu
    exact coveredMeetingOrderedTailSliceAt_disjoint S Y hiu
  rw [coveredMeetingOrderedTailSlices, Finset.card_biUnion hpairwise]
  exact Finset.sum_le_sum fun i hi ↦
    pow_padding_sub_meetingIndex_le_card_coveredMeetingOrderedAt
      R B Y S i hcards hYcover

/-- Clean meeting slices lie inside the complete lower signature union. -/
theorem coveredMeetingOrderedTailSlices_subset_rootAndSignatureUnion
    (R Y : Finset (Fin m)) (S : Finset (Finset (Fin m))) :
    coveredMeetingOrderedTailSlices S Y ⊆
      rootAndBlockedSignatureSubsetUnion R S := by
  classical
  intro U hU
  have hi : ∃ i, U ∈ coveredMeetingOrderedTailSliceAt S Y i := by
    simpa [coveredMeetingOrderedTailSlices] using hU
  rcases hi with ⟨i, hUi⟩
  rcases Finset.mem_biUnion.mp (by
      simpa [coveredMeetingOrderedTailSliceAt,
        coveredSingletonTailSliceAt] using hUi) with
    ⟨C, hC, hUC⟩
  split at hUC
  next hlC =>
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨C, hC,
        blockedSignatureSingletonTailSlice_subset C
          (orderedTailPrefix Y i) (orderedTailCoordinate Y i)
          (Finset.mem_sdiff.mpr hlC) hUC⟩)
  next hlC => simp at hUC

/-- The root lower face and every clean meeting slice are disjoint because
each slice contains a coordinate of `Y ⊆ B ⊆ R`. -/
theorem blockedSignatureSubsetLayer_disjoint_coveredMeetingOrderedTailSlices
    (R B Y : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hYB : Y ⊆ B) (hBR : B ⊆ R) :
    Disjoint (blockedSignatureSubsetLayer R)
      (coveredMeetingOrderedTailSlices S Y) := by
  classical
  rw [Finset.disjoint_left]
  intro U hUR hUO
  have hi : ∃ i, U ∈ coveredMeetingOrderedTailSliceAt S Y i := by
    simpa [coveredMeetingOrderedTailSlices] using hUO
  rcases hi with ⟨i, hUi⟩
  let l := orderedTailCoordinate Y i
  have hInter : U ∩ orderedTailPrefix Y i = {l} := by
    exact inter_tail_eq_singleton_of_mem_coveredAt
      S (orderedTailPrefix Y i) l (by
        simpa [coveredMeetingOrderedTailSliceAt, l] using hUi)
  have hlInter : l ∈ U ∩ orderedTailPrefix Y i := by rw [hInter]; simp
  have hlU := (Finset.mem_inter.mp hlInter).1
  have hlY : l ∈ Y := orderedTailCoordinate_mem Y i
  have hlAllowed := Finset.mem_powerset.mp hUR hlU
  exact (Finset.mem_sdiff.mp hlAllowed).2 (hBR (hYB hlY))

/-- Root, clean meeting slices, and both upper faces fit in one Boolean cube.
The root lower face has the same cardinality as the overlap of the two upper
faces, so those terms cancel exactly and leave the full clean geometric
surplus on the left. -/
theorem orderedMeetingTailSurplus_add_twoUpperFaces_le_fullCube
    (R A B Y : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hABR : A ∪ B = R)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hYB : Y ⊆ B)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hYcover : Y ⊆ S.biUnion (fun C ↦ B \ C))
    (hAmeet : ∀ C ∈ S, (A ∩ C).Nonempty)
    (hBmeet : ∀ C ∈ S, (B ∩ C).Nonempty) :
    orderedMeetingTailSurplus (m - R.card) Y.card +
        (blockedSignatureUpperSubsetLayer A).card +
          (blockedSignatureUpperSubsetLayer B).card ≤ 2 ^ m := by
  classical
  let Root := blockedSignatureSubsetLayer R
  let O := coveredMeetingOrderedTailSlices S Y
  let L := Root ∪ O
  let Upper := twoBlockedSignatureUpperSubsetLayers A B
  let F := L ∪ Upper
  have hAsub : A ⊆ R := by
    rw [← hABR]
    exact Finset.subset_union_left
  have hBsub : B ⊆ R := by
    rw [← hABR]
    exact Finset.subset_union_right
  have hAR : (A ∩ R).Nonempty := by
    obtain ⟨a, ha⟩ := hA
    exact ⟨a, Finset.mem_inter.mpr ⟨ha, hAsub ha⟩⟩
  have hBR : (B ∩ R).Nonempty := by
    obtain ⟨b, hb⟩ := hB
    exact ⟨b, Finset.mem_inter.mpr ⟨hb, hBsub hb⟩⟩
  have hRootO : Disjoint Root O := by
    exact blockedSignatureSubsetLayer_disjoint_coveredMeetingOrderedTailSlices
      R B Y S hYB hBsub
  have hLcard : L.card = Root.card + O.card := by
    exact Finset.card_union_of_disjoint hRootO
  have hLsub : L ⊆ rootAndBlockedSignatureSubsetUnion R S := by
    intro U hU
    rcases Finset.mem_union.mp hU with hURoot | hUO
    · exact Finset.mem_union_left _ hURoot
    · exact coveredMeetingOrderedTailSlices_subset_rootAndSignatureUnion
        R Y S hUO
  have hUpperLower : Disjoint Upper
      (rootAndBlockedSignatureSubsetUnion R S) := by
    exact twoBlockedSignatureUpperSubsetLayers_disjoint_rootAndUnion
      A B R S hAR hBR hAmeet hBmeet
  have hLUpper : Disjoint L Upper :=
    (hUpperLower.mono_right hLsub).symm
  have hFcard : F.card = L.card + Upper.card := by
    exact Finset.card_union_of_disjoint hLUpper
  have hupperIdentity : Upper.card +
      (blockedSignatureUpperSubsetLayer (A ∪ B)).card =
        (blockedSignatureUpperSubsetLayer A).card +
          (blockedSignatureUpperSubsetLayer B).card := by
    have hupper := Finset.card_union_add_card_inter
      (blockedSignatureUpperSubsetLayer A)
      (blockedSignatureUpperSubsetLayer B)
    rw [blockedSignatureUpperSubsetLayers_inter] at hupper
    simpa [Upper, twoBlockedSignatureUpperSubsetLayers] using hupper
  have hrootUpper : Root.card =
      (blockedSignatureUpperSubsetLayer (A ∪ B)).card := by
    change (blockedSignatureSubsetLayer R).card =
      (blockedSignatureUpperSubsetLayer (A ∪ B)).card
    rw [card_blockedSignatureUpperSubsetLayer, hABR,
      card_blockedSignatureSubsetLayer]
  have hFidentity : F.card = O.card +
      (blockedSignatureUpperSubsetLayer A).card +
        (blockedSignatureUpperSubsetLayer B).card := by
    omega
  have hFcube : F.card ≤ 2 ^ m := by
    have hsubset : F ⊆ (Finset.univ : Finset (Fin m)).powerset := by
      intro U _
      exact Finset.mem_powerset.mpr (Finset.subset_univ U)
    calc
      F.card ≤ ((Finset.univ : Finset (Fin m)).powerset).card :=
        Finset.card_mono hsubset
      _ = 2 ^ m := by
        rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  have hOcard : orderedMeetingTailSurplus (m - R.card) Y.card ≤ O.card := by
    simpa [O] using
      orderedMeetingTailSurplus_le_card_coveredMeetingOrderedSlices
        R B Y S hcards hYcover
  calc
    orderedMeetingTailSurplus (m - R.card) Y.card +
        (blockedSignatureUpperSubsetLayer A).card +
          (blockedSignatureUpperSubsetLayer B).card ≤
      O.card + (blockedSignatureUpperSubsetLayer A).card +
        (blockedSignatureUpperSubsetLayer B).card :=
      by omega
    _ = F.card := hFidentity.symm
    _ ≤ 2 ^ m := hFcube

section CollisionMeetingOrderedSlices

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Actual collision form: every tail subset `Y` covered by positive-tail-
meeting signatures contributes its clean geometric surplus alongside both
upper faces. -/
theorem orderedMeetingTailSurplus_add_tailUpperFaces_le_fullCube
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hA : r.val.1.Nonempty)
    (Y : Finset (Fin m)) (hYB : Y ⊆ r.val.2)
    (hYmeet : Y ⊆ positiveTailMeetingBlockedSignatureCoverage hh r) :
    orderedMeetingTailSurplus
        (m - (reducedCollisionSupport r).card) Y.card +
        2 ^ (m - r.val.1.card) + 2 ^ (m - r.val.2.card) ≤ 2 ^ m := by
  classical
  let R := reducedCollisionSupport r
  let S := positiveTailMeetingEscapeBlockedSignatures hh r
  have hB := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  have hcards : ∀ C ∈ S, C.card = R.card := by
    intro C hC
    have hC' := mem_positiveTailMeetingEscapeBlockedSignatures_iff.mp hC
    exact card_escapeBlockedSignature_eq_rootSupport hh r hrmin hC'.1
  have hYcover : Y ⊆ S.biUnion (fun C ↦ r.val.2 \ C) := by
    change Y ⊆ S.biUnion (blockedSignatureEscapeFiber r) at hYmeet
    exact hYmeet
  have hAmeet : ∀ C ∈ S, (r.val.1 ∩ C).Nonempty := by
    intro C hC
    exact (mem_positiveTailMeetingEscapeBlockedSignatures_iff.mp hC).2
  have hBmeet : ∀ C ∈ S, (r.val.2 ∩ C).Nonempty := by
    intro C hC
    have hC' := mem_positiveTailMeetingEscapeBlockedSignatures_iff.mp hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC'.1
  have hbound := orderedMeetingTailSurplus_add_twoUpperFaces_le_fullCube
    R r.val.1 r.val.2 Y S rfl hA hB hYB hcards hYcover hAmeet hBmeet
  simpa [card_blockedSignatureUpperSubsetLayer,
    card_blockedSignatureSubsetLayer] using hbound

/-- The genuine critical residual simultaneously retains the exact
avoiding/meeting partition, the crossing bound on the avoiding part, and the
clean geometric face inequality on the meeting part. -/
theorem genuineDominant_avoidingCharge_and_meetingGeometricFaces
    {n s q : ℕ} (hn : 1 ≤ n) (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    let X := positiveTailAvoidingCoveredSourceTail hh r
    let Y := r.val.2 \ X
    X ⊆ r.val.2 ∧ X.card + Y.card = r.val.2.card ∧
      Y ⊆ positiveTailMeetingBlockedSignatureCoverage hh r ∧
      16 * X.card * r.val.2.card <
        criticalHalfGap n s * criticalHalfGap n s ∧
      orderedMeetingTailSurplus
          (n - (reducedCollisionSupport r).card) Y.card +
          2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card) ≤ 2 ^ n := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  let X := positiveTailAvoidingCoveredSourceTail hh r
  let Y := r.val.2 \ X
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card := by
    simpa [hh, criticalCanonicalReducedCollisions,
      reducedCollisionSupport] using hdominant.2.1
  have hpartition := genuineDominant_tailCoverage_partition
    hqodd g hg r hr hres
  have hpartition' : X ⊆ r.val.2 ∧
      X.card + Y.card = r.val.2.card ∧
      Y ⊆ positiveTailMeetingBlockedSignatureCoverage hh r ∧
      16 * X.card * r.val.2.card <
        criticalHalfGap n s * criticalHalfGap n s := by
    simpa [hh, X, Y] using hpartition
  have hA := genuineDominant_positiveTail_nonempty hn hqodd g hg r hr hres
  have hfaces := orderedMeetingTailSurplus_add_tailUpperFaces_le_fullCube
    hg hh (half_ne_zero hN hM) r hr' hrmin hA Y
      (by exact Finset.sdiff_subset) hpartition'.2.2.1
  exact ⟨hpartition'.1, hpartition'.2.1, hpartition'.2.2.1,
    hpartition'.2.2.2, hfaces⟩

end CollisionMeetingOrderedSlices

end MinModulus
