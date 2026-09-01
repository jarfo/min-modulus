/-
# Positive-tail upper face or a reverse canonical crossing

Every escape signature meets the source negative tail, which supplied the
first disjoint upper face.  The source positive tail gives the next exact
split.  If every signature also meets `A_r`, then both the `A_r`- and
`B_r`-upper faces are disjoint from the lower signature union.  Their overlap
is exactly the upper face of the full root support, so inclusion-exclusion is
exact.

If a signature does not meet `A_r`, choose an actual escape target realizing
it.  Restoration preserves membership on root coordinates, so that target
does not cross from `A_r`.  The canonical pairwise-crossing theorem therefore
forces the reverse orientation: the target positive tail crosses into `B_r`.
-/
import MinModulus.G1SignatureIntersectingCoverage

namespace MinModulus

open Finset

section TwoUpperFaces

variable {m : ℕ}

/-- Two upper Boolean faces. -/
noncomputable def twoBlockedSignatureUpperSubsetLayers
    (T U : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  blockedSignatureUpperSubsetLayer T ∪
    blockedSignatureUpperSubsetLayer U

/-- The intersection of two upper faces is the upper face of the union of
their forced-coordinate sets. -/
theorem blockedSignatureUpperSubsetLayers_inter
    (T U : Finset (Fin m)) :
    blockedSignatureUpperSubsetLayer T ∩
        blockedSignatureUpperSubsetLayer U =
      blockedSignatureUpperSubsetLayer (T ∪ U) := by
  classical
  ext V
  simp only [Finset.mem_inter, mem_blockedSignatureUpperSubsetLayer_iff]
  exact Finset.union_subset_iff.symm

/-- If both forced-coordinate sets hit the root and every signature, their
upper-face union is disjoint from the complete lower union. -/
theorem twoBlockedSignatureUpperSubsetLayers_disjoint_rootAndUnion
    (T U R : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hTR : (T ∩ R).Nonempty) (hUR : (U ∩ R).Nonempty)
    (hT : ∀ C ∈ S, (T ∩ C).Nonempty)
    (hU : ∀ C ∈ S, (U ∩ C).Nonempty) :
    Disjoint (twoBlockedSignatureUpperSubsetLayers T U)
      (rootAndBlockedSignatureSubsetUnion R S) := by
  classical
  rw [Finset.disjoint_left]
  intro V hV hLower
  rcases Finset.mem_union.mp hV with hVT | hVU
  · exact (Finset.disjoint_left.mp
      (blockedSignatureUpperSubsetLayer_disjoint_rootAndUnion
        T R S hTR hT)) hVT hLower
  · exact (Finset.disjoint_left.mp
      (blockedSignatureUpperSubsetLayer_disjoint_rootAndUnion
        U R S hUR hU)) hVU hLower

/-- The lower union enlarged by two hitting upper faces. -/
noncomputable def rootAndBlockedSignatureSubsetUnionWithTwoUpper
    (T U R : Finset (Fin m)) (S : Finset (Finset (Fin m))) :
    Finset (Finset (Fin m)) :=
  rootAndBlockedSignatureSubsetUnion R S ∪
    twoBlockedSignatureUpperSubsetLayers T U

/-- Exact inclusion-exclusion identity after adjoining two upper faces. -/
theorem card_unionWithTwoUpper_add_upperUnion
    (T U R : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hTR : (T ∩ R).Nonempty) (hUR : (U ∩ R).Nonempty)
    (hT : ∀ C ∈ S, (T ∩ C).Nonempty)
    (hU : ∀ C ∈ S, (U ∩ C).Nonempty) :
    (rootAndBlockedSignatureSubsetUnionWithTwoUpper T U R S).card +
        (blockedSignatureUpperSubsetLayer (T ∪ U)).card =
      (rootAndBlockedSignatureSubsetUnion R S).card +
        (blockedSignatureUpperSubsetLayer T).card +
          (blockedSignatureUpperSubsetLayer U).card := by
  classical
  have hdisj :=
    twoBlockedSignatureUpperSubsetLayers_disjoint_rootAndUnion
      T U R S hTR hUR hT hU
  have hcombined :
      (rootAndBlockedSignatureSubsetUnionWithTwoUpper T U R S).card =
        (rootAndBlockedSignatureSubsetUnion R S).card +
          (twoBlockedSignatureUpperSubsetLayers T U).card := by
    rw [rootAndBlockedSignatureSubsetUnionWithTwoUpper,
      Finset.card_union_of_disjoint hdisj.symm]
  have hupper := Finset.card_union_add_card_inter
    (blockedSignatureUpperSubsetLayer T)
    (blockedSignatureUpperSubsetLayer U)
  rw [blockedSignatureUpperSubsetLayers_inter] at hupper
  change (twoBlockedSignatureUpperSubsetLayers T U).card +
      (blockedSignatureUpperSubsetLayer (T ∪ U)).card = _ at hupper
  omega

/-- Exact factor-two lower growth plus both hitting upper faces. -/
theorem two_mul_root_add_twoUpper_le_unionWithTwoUpper_add_upperUnion
    (T U R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hBinter : ∀ C ∈ S, (B ∩ C).Nonempty)
    (hTR : (T ∩ R).Nonempty) (hUR : (U ∩ R).Nonempty)
    (hT : ∀ C ∈ S, (T ∩ C).Nonempty)
    (hU : ∀ C ∈ S, (U ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        (blockedSignatureUpperSubsetLayer T).card +
          (blockedSignatureUpperSubsetLayer U).card ≤
      (rootAndBlockedSignatureSubsetUnionWithTwoUpper T U R S).card +
        (blockedSignatureUpperSubsetLayer (T ∪ U)).card := by
  have hlower := two_mul_root_le_covered_signature_union_of_inter_nonempty
    R B S hB hBR hcards hcover hBinter
  have hcard := card_unionWithTwoUpper_add_upperUnion
    T U R S hTR hUR hT hU
  omega

/-- Full Boolean-cube consequence of the two-upper-face count. -/
theorem two_mul_root_add_twoUpper_le_fullCube_add_upperUnion
    (T U R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hBinter : ∀ C ∈ S, (B ∩ C).Nonempty)
    (hTR : (T ∩ R).Nonempty) (hUR : (U ∩ R).Nonempty)
    (hT : ∀ C ∈ S, (T ∩ C).Nonempty)
    (hU : ∀ C ∈ S, (U ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        (blockedSignatureUpperSubsetLayer T).card +
          (blockedSignatureUpperSubsetLayer U).card ≤
      2 ^ m + (blockedSignatureUpperSubsetLayer (T ∪ U)).card := by
  classical
  have hcount :=
    two_mul_root_add_twoUpper_le_unionWithTwoUpper_add_upperUnion
      T U R B S hB hBR hcards hcover hBinter hTR hUR hT hU
  have hsubset : rootAndBlockedSignatureSubsetUnionWithTwoUpper T U R S ⊆
      (Finset.univ : Finset (Fin m)).powerset := by
    intro V _
    exact Finset.mem_powerset.mpr (Finset.subset_univ V)
  calc
    2 * (blockedSignatureSubsetLayer R).card +
        (blockedSignatureUpperSubsetLayer T).card +
          (blockedSignatureUpperSubsetLayer U).card ≤
      (rootAndBlockedSignatureSubsetUnionWithTwoUpper T U R S).card +
        (blockedSignatureUpperSubsetLayer (T ∪ U)).card := hcount
    _ ≤ ((Finset.univ : Finset (Fin m)).powerset).card +
        (blockedSignatureUpperSubsetLayer (T ∪ U)).card :=
      Nat.add_le_add_right (Finset.card_mono hsubset) _
    _ = 2 ^ m + (blockedSignatureUpperSubsetLayer (T ∪ U)).card := by
      rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]

end TwoUpperFaces

section PositiveTailApplication

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A realized signature either meets the source positive tail or its target
is forced into the reverse oriented crossing `(q,r)`. -/
theorem all_escapeSignatures_meet_positiveTail_or_exists_reverseCross
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card) :
    (∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.1 ∩ C).Nonempty) ∨
    ∃ q ∈ canonicalSupportEscapeTargets hh r,
      (q, r) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh := by
  classical
  by_cases hall : ∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.1 ∩ C).Nonempty
  · exact Or.inl hall
  · right
    push Not at hall
    rcases hall with ⟨C, hC, hAC⟩
    rcases mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC with
      ⟨q, hqtarget, hqC⟩
    rcases mem_canonicalSupportEscapeTargets_iff.mp hqtarget with ⟨j, hjq⟩
    have hjq' := mem_canonicalSupportEscapeIncidences_iff.mp hjq
    have hqr := reducedCollision_ne_of_right_mem_of_avoids
      r q hjq'.1 hjq'.2.2.1
    have hnotForward : ¬(r.val.1 ∩ q.val.2).Nonempty := by
      intro hforward
      obtain ⟨k, hk⟩ := hforward
      have hkrA := (Finset.mem_inter.mp hk).1
      have hkqB := (Finset.mem_inter.mp hk).2
      have hkAC : k ∈ r.val.1 ∩ C := by
        refine Finset.mem_inter.mpr ⟨hkrA, ?_⟩
        rw [← hqC]
        exact (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
            r q (hrmin q hjq'.2.1) (Finset.mem_union_left _ hkrA)).2
          (Finset.mem_union_right _ hkqB)
      rw [hAC] at hkAC
      simp at hkAC
    have hcross := distinct_canonicalReducedCollisions_positive_negative_cross
      g hg hh hh0 r q
        (mem_canonicalReducedCollisions_iff.mp hr)
        (mem_canonicalReducedCollisions_iff.mp hjq'.2.1) hqr
    rcases hcross with hforward | hreverse
    · exact False.elim (hnotForward hforward)
    · exact ⟨q, hqtarget,
        mem_canonicalPositiveNegativeCrossPairs_iff.mpr
          ⟨hjq'.2.1, hr, hqr, hreverse⟩⟩

/-- Value-level lower union enlarged by both source-tail upper faces. -/
noncomputable def rootAndEscapeBlockedSignatureValueUnionWithTailUpperFaces
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset G :=
  rootAndEscapeBlockedSignatureValueUnion hh r ∪
    (blockedSignatureUpperValueLayer g r.val.1 ∪
      blockedSignatureUpperValueLayer g r.val.2)

/-- The two-upper-face subset union maps exactly to its value union. -/
theorem image_rootAndEscapeBlockedSignatureSubsetUnionWithTailUpperFaces
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (rootAndBlockedSignatureSubsetUnionWithTwoUpper r.val.1 r.val.2
        (reducedCollisionSupport r)
        (canonicalSupportEscapeBlockedSignatures hh r)).image (ssum g) =
      rootAndEscapeBlockedSignatureValueUnionWithTailUpperFaces hh r := by
  classical
  rw [rootAndBlockedSignatureSubsetUnionWithTwoUpper,
    twoBlockedSignatureUpperSubsetLayers, Finset.image_union,
    Finset.image_union, image_rootAndEscapeBlockedSignatureSubsetUnion]
  rfl

/-- If every signature meets the positive tail, the two upper faces give the
exact enriched value-layer count, with their root-upper overlap charged on
the right. -/
theorem two_weight_add_tailUpperFaces_le_unionWithTailUpperFaces_add_weight
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2)
    (hpositive : ∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.1 ∩ C).Nonempty) :
    2 * reducedCollisionWeight (m := m) r + 2 ^ (m - r.val.1.card) +
        2 ^ (m - r.val.2.card) ≤
      (rootAndEscapeBlockedSignatureValueUnionWithTailUpperFaces hh r).card +
        reducedCollisionWeight (m := m) r := by
  classical
  let R := reducedCollisionSupport r
  let S := canonicalSupportEscapeBlockedSignatures hh r
  have hB := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  have hBR : r.val.2 ⊆ R := by
    intro j hj
    exact Finset.mem_union_right _ hj
  have hcards : ∀ C ∈ S, C.card = R.card := by
    intro C hC
    exact card_escapeBlockedSignature_eq_rootSupport hh r hrmin hC
  have hcover' : S.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 := by
    change canonicalSupportEscapeBlockedSignatureCoverage hh r = r.val.2
    exact hcover
  have hBinter : ∀ C ∈ S, (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hA : r.val.1.Nonempty := by
    have hS : S.Nonempty := by
      obtain ⟨j, hjB⟩ := hB
      have hjCover : j ∈ S.biUnion (fun C ↦ r.val.2 \ C) := by
        rw [hcover']
        exact hjB
      rcases Finset.mem_biUnion.mp hjCover with ⟨C, hC, _⟩
      exact ⟨C, hC⟩
    obtain ⟨C, hC⟩ := hS
    obtain ⟨j, hj⟩ := hpositive C hC
    exact ⟨j, (Finset.mem_inter.mp hj).1⟩
  have hAR : (r.val.1 ∩ R).Nonempty := by
    obtain ⟨j, hjA⟩ := hA
    exact ⟨j, Finset.mem_inter.mpr
      ⟨hjA, Finset.mem_union_left _ hjA⟩⟩
  have hBRinter : (r.val.2 ∩ R).Nonempty := by
    obtain ⟨j, hjB⟩ := hB
    exact ⟨j, Finset.mem_inter.mpr
      ⟨hjB, Finset.mem_union_right _ hjB⟩⟩
  have hsubset :=
    two_mul_root_add_twoUpper_le_unionWithTwoUpper_add_upperUnion
      r.val.1 r.val.2 R r.val.2 S hB hBR hcards hcover' hBinter
        hAR hBRinter hpositive hBinter
  have hrootCard :
      (blockedSignatureSubsetLayer R).card =
        reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  have hunionCard :
      (rootAndBlockedSignatureSubsetUnionWithTwoUpper r.val.1 r.val.2 R S).card =
        (rootAndEscapeBlockedSignatureValueUnionWithTailUpperFaces hh r).card := by
    rw [← image_rootAndEscapeBlockedSignatureSubsetUnionWithTailUpperFaces hh r,
      Finset.card_image_of_injective _ (ssum_injective g hg)]
  have hupperRoot :
      (blockedSignatureUpperSubsetLayer (r.val.1 ∪ r.val.2)).card =
        reducedCollisionWeight (m := m) r := by
    rw [card_blockedSignatureUpperSubsetLayer]
    simpa [R, reducedCollisionSupport] using hrootCard
  simpa [hrootCard, hunionCard, hupperRoot,
    card_blockedSignatureUpperSubsetLayer,
    card_blockedSignatureSubsetLayer] using hsubset

/-- Full-cube numerical constraint in the all-positive-incidence branch. -/
theorem two_weight_add_tailUpperFaces_le_fullCube_add_weight
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2)
    (hpositive : ∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.1 ∩ C).Nonempty) :
    2 * reducedCollisionWeight (m := m) r + 2 ^ (m - r.val.1.card) +
        2 ^ (m - r.val.2.card) ≤
      2 ^ m + reducedCollisionWeight (m := m) r := by
  classical
  let R := reducedCollisionSupport r
  let S := canonicalSupportEscapeBlockedSignatures hh r
  have hB := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  have hBR : r.val.2 ⊆ R := by
    intro j hj
    exact Finset.mem_union_right _ hj
  have hcards : ∀ C ∈ S, C.card = R.card := by
    intro C hC
    exact card_escapeBlockedSignature_eq_rootSupport hh r hrmin hC
  have hcover' : S.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 := by
    change canonicalSupportEscapeBlockedSignatureCoverage hh r = r.val.2
    exact hcover
  have hBinter : ∀ C ∈ S, (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hA : r.val.1.Nonempty := by
    have hS : S.Nonempty := by
      obtain ⟨j, hjB⟩ := hB
      have hjCover : j ∈ S.biUnion (fun C ↦ r.val.2 \ C) := by
        rw [hcover']
        exact hjB
      rcases Finset.mem_biUnion.mp hjCover with ⟨C, hC, _⟩
      exact ⟨C, hC⟩
    obtain ⟨C, hC⟩ := hS
    obtain ⟨j, hj⟩ := hpositive C hC
    exact ⟨j, (Finset.mem_inter.mp hj).1⟩
  have hAR : (r.val.1 ∩ R).Nonempty := by
    obtain ⟨j, hjA⟩ := hA
    exact ⟨j, Finset.mem_inter.mpr
      ⟨hjA, Finset.mem_union_left _ hjA⟩⟩
  have hBRinter : (r.val.2 ∩ R).Nonempty := by
    obtain ⟨j, hjB⟩ := hB
    exact ⟨j, Finset.mem_inter.mpr
      ⟨hjB, Finset.mem_union_right _ hjB⟩⟩
  have hsubset := two_mul_root_add_twoUpper_le_fullCube_add_upperUnion
    r.val.1 r.val.2 R r.val.2 S hB hBR hcards hcover' hBinter
      hAR hBRinter hpositive hBinter
  have hrootCard :
      (blockedSignatureSubsetLayer R).card =
        reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  have hupperRoot :
      (blockedSignatureUpperSubsetLayer (r.val.1 ∪ r.val.2)).card =
        reducedCollisionWeight (m := m) r := by
    rw [card_blockedSignatureUpperSubsetLayer]
    simpa [R, reducedCollisionSupport] using hrootCard
  simpa [hrootCard, hupperRoot,
    card_blockedSignatureUpperSubsetLayer,
    card_blockedSignatureSubsetLayer] using hsubset

/-- Operational positive-tail split: an actual escape target crosses back
into the root negative tail, or both upper faces satisfy the full-cube bound. -/
theorem exists_escapeTarget_reverseCross_or_twoTailUpperFaces_fullCube
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    (∃ q ∈ canonicalSupportEscapeTargets hh r,
      (q, r) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh) ∨
    2 * reducedCollisionWeight (m := m) r + 2 ^ (m - r.val.1.card) +
        2 ^ (m - r.val.2.card) ≤
      2 ^ m + reducedCollisionWeight (m := m) r := by
  rcases all_escapeSignatures_meet_positiveTail_or_exists_reverseCross
      hg hh hh0 r hr hrmin with hpositive | hcross
  · exact Or.inr (two_weight_add_tailUpperFaces_le_fullCube_add_weight
      hg hh hh0 r hr hrmin hcover hpositive)
  · exact Or.inl hcross

end PositiveTailApplication

end MinModulus
