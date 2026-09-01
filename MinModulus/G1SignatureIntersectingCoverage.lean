/-
# Intersecting signature coverage forces a full factor two

The sharp coverage theorem allowed a branch in which one signature drops the
entire source tail.  Canonical negative-tail intersection rules that branch
out: every realized blocked signature meets `B_r`, while the relative
complements of those same signatures cover `B_r`.

Consequently two dropped fibers must be incomparable.  Their private
coordinate half-cubes and the root give a full `2 w_r` lower union, with no
`2^-|B_r|` loss.  The disjoint `B_r`-upper face from the preceding module then
gives `2 w_r + 2^(m-|B_r|)` distinct anchored subset-sum values.
-/
import MinModulus.G1SignatureUpperFace

namespace MinModulus

open Finset

variable {α : Type*} [DecidableEq α]

/-- If every covering set still meets `B`, no single relative complement can
cover `B`; hence the cover contains two incomparable relative complements. -/
theorem finset_sdiff_cover_incomparable_of_inter_nonempty
    (S : Finset (Finset α)) (B : Finset α) (hB : B.Nonempty)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    ∃ C ∈ S, ∃ D ∈ S,
      ((B \ C) \ (B \ D)).Nonempty ∧
        ((B \ D) \ (B \ C)).Nonempty := by
  rcases finset_sdiff_cover_single_or_incomparable S B hB hcover with
    hsingle | hincomparable
  · rcases hsingle with ⟨C, hC, hdrop⟩
    obtain ⟨j, hj⟩ := hinter C hC
    have hjB := (Finset.mem_inter.mp hj).1
    have hjC := (Finset.mem_inter.mp hj).2
    exact False.elim ((Finset.mem_sdiff.mp (hdrop hjB)).2 hjC)
  · exact hincomparable

section IntersectingSubcubes

variable {m : ℕ}

/-- Intersecting coordinate coverage improves the sharp almost-two estimate
to a full factor-two lower bound. -/
theorem two_mul_root_le_covered_signature_union_of_inter_nonempty
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card ≤
      (rootAndBlockedSignatureSubsetUnion R S).card := by
  classical
  rcases finset_sdiff_cover_incomparable_of_inter_nonempty
      S B hB hcover hinter with ⟨C, hC, D, hD, hinc⟩
  have hthree :=
    two_mul_card_blockedSignatureSubsetLayer_le_three_union_of_incomparable
      R C D B hBR (hcards C hC) (hcards D hD) hinc
  have hsubset :
      blockedSignatureSubsetLayer R ∪ blockedSignatureSubsetLayer C ∪
          blockedSignatureSubsetLayer D ⊆
        rootAndBlockedSignatureSubsetUnion R S := by
    intro U hU
    rcases Finset.mem_union.mp hU with hURC | hUD
    · rcases Finset.mem_union.mp hURC with hUR | hUC
      · exact Finset.mem_union_left _ hUR
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨C, hC, hUC⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨D, hD, hUD⟩)
  exact hthree.trans (Finset.card_mono hsubset)

/-- Adding the disjoint `B`-upper face to the full factor-two lower union. -/
theorem two_mul_root_add_tailFace_le_unionWithUpper_of_inter_nonempty
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        (blockedSignatureSubsetLayer B).card ≤
      (rootAndBlockedSignatureSubsetUnionWithUpper B R S).card := by
  classical
  have hlower := two_mul_root_le_covered_signature_union_of_inter_nonempty
    R B S hB hBR hcards hcover hinter
  have hBRinter : (B ∩ R).Nonempty := by
    obtain ⟨j, hjB⟩ := hB
    exact ⟨j, Finset.mem_inter.mpr ⟨hjB, hBR hjB⟩⟩
  rw [card_rootAndBlockedSignatureSubsetUnionWithUpper
    B R S hBRinter hinter]
  exact Nat.add_le_add_right hlower _

/-- The corresponding unscaled numerical constraint inside the full Boolean
cube. -/
theorem two_mul_root_add_tailFace_le_fullCube_of_inter_nonempty
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        (blockedSignatureSubsetLayer B).card ≤ 2 ^ m := by
  classical
  have henriched :=
    two_mul_root_add_tailFace_le_unionWithUpper_of_inter_nonempty
      R B S hB hBR hcards hcover hinter
  have hsubset : rootAndBlockedSignatureSubsetUnionWithUpper B R S ⊆
      (Finset.univ : Finset (Fin m)).powerset := by
    intro U _
    exact Finset.mem_powerset.mpr (Finset.subset_univ U)
  calc
    2 * (blockedSignatureSubsetLayer R).card +
        (blockedSignatureSubsetLayer B).card ≤
      (rootAndBlockedSignatureSubsetUnionWithUpper B R S).card := henriched
    _ ≤ ((Finset.univ : Finset (Fin m)).powerset).card :=
      Finset.card_mono hsubset
    _ = 2 ^ m := by
      rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]

end IntersectingSubcubes

section CriticalIntersectingCoverage

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The actual root-plus-signature value union has at least two full dominant
weights. -/
theorem two_mul_weight_le_escapeBlockedSignatureValueUnion
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    2 * reducedCollisionWeight (m := m) r ≤
      (rootAndEscapeBlockedSignatureValueUnion hh r).card := by
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
  have hinter : ∀ C ∈ S, (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hsubset := two_mul_root_le_covered_signature_union_of_inter_nonempty
    R r.val.2 S hB hBR hcards hcover' hinter
  have hrootCard :
      (blockedSignatureSubsetLayer R).card =
        reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  have hunionCard :
      (rootAndBlockedSignatureSubsetUnion R S).card =
        (rootAndEscapeBlockedSignatureValueUnion hh r).card := by
    rw [← image_rootAndEscapeBlockedSignatureSubsetUnion hh r,
      Finset.card_image_of_injective _ (ssum_injective g hg)]
  simpa [hrootCard, hunionCard] using hsubset

/-- The actual enriched value union contains two root weights plus the entire
`B_r`-upper face. -/
theorem two_mul_weight_add_tailFace_le_escapeValueUnionWithUpper
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    2 * reducedCollisionWeight (m := m) r + 2 ^ (m - r.val.2.card) ≤
      (rootAndEscapeBlockedSignatureValueUnionWithUpper hh r).card := by
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
  have hinter : ∀ C ∈ S, (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hsubset :=
    two_mul_root_add_tailFace_le_unionWithUpper_of_inter_nonempty
      R r.val.2 S hB hBR hcards hcover' hinter
  have hrootCard :
      (blockedSignatureSubsetLayer R).card =
        reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  have hunionCard :
      (rootAndBlockedSignatureSubsetUnionWithUpper r.val.2 R S).card =
        (rootAndEscapeBlockedSignatureValueUnionWithUpper hh r).card := by
    rw [← image_rootAndEscapeBlockedSignatureSubsetUnionWithUpper hh r,
      Finset.card_image_of_injective _ (ssum_injective g hg)]
  simpa [hrootCard, hunionCard,
    card_blockedSignatureSubsetLayer] using hsubset

/-- Unscaled full-cube consequence of intersecting signature coverage. -/
theorem two_mul_weight_add_tailFace_le_fullCube
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    2 * reducedCollisionWeight (m := m) r + 2 ^ (m - r.val.2.card) ≤
      2 ^ m := by
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
  have hinter : ∀ C ∈ S, (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hsubset := two_mul_root_add_tailFace_le_fullCube_of_inter_nonempty
    R r.val.2 S hB hBR hcards hcover' hinter
  have hrootCard :
      (blockedSignatureSubsetLayer R).card =
        reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  simpa [hrootCard, card_blockedSignatureSubsetLayer] using hsubset

end CriticalIntersectingCoverage

end MinModulus
