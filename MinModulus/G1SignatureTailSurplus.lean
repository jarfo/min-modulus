/-
# Linear tail surplus in covered signature subcubes

Intersecting signature coverage was previously used only to obtain two
private half-cubes and hence a factor `2` times the root weight.  The same
construction contains a further uniform surplus.  The two private
coordinates account for the two half-cubes; every other coordinate of the
covered tail contributes its singleton subset, which lies in some signature
layer and outside the counted root/private-half-cube family.

Consequently the complete lower union has at least `2w + |B| - 2` elements,
expressed without truncated subtraction as `2w + |B| ≤ |union| + 2`.
-/
import MinModulus.G1TailCoveragePartition

namespace MinModulus

open Finset

variable {m : ℕ}

/-- The family of singleton subsets indexed by a finite coordinate set. -/
def singletonSubsetFamily (B : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  B.image (fun j ↦ {j})

@[simp] theorem mem_singletonSubsetFamily_iff
    {B : Finset (Fin m)} {U : Finset (Fin m)} :
    U ∈ singletonSubsetFamily B ↔ ∃ j ∈ B, U = {j} := by
  classical
  constructor
  · intro hU
    rcases Finset.mem_image.mp hU with ⟨j, hj, hUj⟩
    exact ⟨j, hj, hUj.symm⟩
  · rintro ⟨j, hj, rfl⟩
    exact Finset.mem_image.mpr ⟨j, hj, rfl⟩

theorem card_singletonSubsetFamily (B : Finset (Fin m)) :
    (singletonSubsetFamily B).card = B.card := by
  classical
  rw [singletonSubsetFamily, Finset.card_image_iff.mpr]
  intro j _ k _ hjk
  simpa using hjk

/-- Sharp linear refinement of the factor-two covered-subcube estimate. -/
theorem two_mul_root_add_tailCard_le_covered_signature_union_add_two
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card + B.card ≤
      (rootAndBlockedSignatureSubsetUnion R S).card + 2 := by
  classical
  rcases finset_sdiff_cover_incomparable_of_inter_nonempty
      S B hB hcover hinter with ⟨C, hC, D, hD, hinc⟩
  obtain ⟨j, hj⟩ := hinc.1
  obtain ⟨k, hk⟩ := hinc.2
  have hjBC : j ∈ B \ C := (Finset.mem_sdiff.mp hj).1
  have hjnotBD : j ∉ B \ D := (Finset.mem_sdiff.mp hj).2
  have hjB : j ∈ B := (Finset.mem_sdiff.mp hjBC).1
  have hjC : j ∉ C := (Finset.mem_sdiff.mp hjBC).2
  have hjD : j ∈ D := by
    by_contra hjD
    exact hjnotBD (Finset.mem_sdiff.mpr ⟨hjB, hjD⟩)
  have hkBD : k ∈ B \ D := (Finset.mem_sdiff.mp hk).1
  have hknotBC : k ∉ B \ C := (Finset.mem_sdiff.mp hk).2
  have hkB : k ∈ B := (Finset.mem_sdiff.mp hkBD).1
  have hkD : k ∉ D := (Finset.mem_sdiff.mp hkBD).2
  have hkC : k ∈ C := by
    by_contra hkC
    exact hknotBC (Finset.mem_sdiff.mpr ⟨hkB, hkC⟩)
  have hjk : j ≠ k := by
    intro hjk
    subst k
    exact hkD hjD
  have hjR : j ∈ R := hBR hjB
  have hkR : k ∈ R := hBR hkB
  let HC := blockedSignatureContainingSubsetLayer C j
  let HD := blockedSignatureContainingSubsetLayer D k
  let K := (blockedSignatureSubsetLayer R ∪ HC) ∪ HD
  let Q := (B.erase j).erase k
  let SQ := singletonSubsetFamily Q
  have hRootC : Disjoint (blockedSignatureSubsetLayer R) HC :=
    (blockedSignatureContainingSubsetLayer_disjoint C R j hjR).symm
  have hRootD : Disjoint (blockedSignatureSubsetLayer R) HD :=
    (blockedSignatureContainingSubsetLayer_disjoint D R k hkR).symm
  have hCD : Disjoint HC HD := by
    exact (blockedSignatureContainingSubsetLayer_disjoint C D j hjD).mono_right
      (blockedSignatureContainingSubsetLayer_subset D k)
  have hRootC_D : Disjoint (blockedSignatureSubsetLayer R ∪ HC) HD := by
    rw [Finset.disjoint_left]
    intro U hU hUHD
    rcases Finset.mem_union.mp hU with hUR | hUHC
    · exact (Finset.disjoint_left.mp hRootD) hUR hUHD
    · exact (Finset.disjoint_left.mp hCD) hUHC hUHD
  have hp : 0 < m - R.card := by
    have hjAllowed : j ∈ Finset.univ \ C := by simp [hjC]
    have hpos : 0 < (Finset.univ \ C).card :=
      Finset.card_pos.mpr ⟨j, hjAllowed⟩
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C)] at hpos
    simpa [hcards C hC] using hpos
  have hhalfC : 2 * HC.card = (blockedSignatureSubsetLayer R).card := by
    rw [card_blockedSignatureSubsetLayer,
      show HC.card = 2 ^ (m - C.card - 1) by
        exact card_blockedSignatureContainingSubsetLayer C j hjC,
      hcards C hC]
    simpa [Nat.mul_comm] using Nat.two_pow_pred_mul_two hp
  have hhalfD : 2 * HD.card = (blockedSignatureSubsetLayer R).card := by
    rw [card_blockedSignatureSubsetLayer,
      show HD.card = 2 ^ (m - D.card - 1) by
        exact card_blockedSignatureContainingSubsetLayer D k hkD,
      hcards D hD]
    simpa [Nat.mul_comm] using Nat.two_pow_pred_mul_two hp
  have hKcard : K.card =
      2 * (blockedSignatureSubsetLayer R).card := by
    have hcard : K.card =
        (blockedSignatureSubsetLayer R).card + HC.card + HD.card := by
      dsimp only [K]
      rw [Finset.card_union_of_disjoint hRootC_D,
        Finset.card_union_of_disjoint hRootC, Nat.add_assoc]
    omega
  have hkQ : k ∈ B.erase j := by simp [hkB, hjk.symm]
  have hQcard : Q.card + 2 = B.card := by
    have hkCard := Finset.card_erase_add_one hkQ
    have hjCard := Finset.card_erase_add_one hjB
    change ((B.erase j).erase k).card + 2 = B.card
    omega
  have hSQcard : SQ.card = Q.card := by
    exact card_singletonSubsetFamily Q
  have hKSQ : Disjoint K SQ := by
    rw [Finset.disjoint_left]
    intro U hUK hUSQ
    rcases mem_singletonSubsetFamily_iff.mp hUSQ with ⟨l, hlQ, rfl⟩
    have hlQ' : l ∈ (B.erase j).erase k := by
      simpa [Q] using hlQ
    have hlB : l ∈ B := by
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hlQ').2).2
    have hlj : l ≠ j := by
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp hlQ').2).1
    have hlk : l ≠ k := (Finset.mem_erase.mp hlQ').1
    rcases Finset.mem_union.mp hUK with hURC | hUHD
    · rcases Finset.mem_union.mp hURC with hUR | hUHC
      · have hallowed := Finset.mem_powerset.mp hUR
        have hlAllowed := hallowed
          (by simp : l ∈ ({l} : Finset (Fin m)))
        exact (Finset.mem_sdiff.mp hlAllowed).2 (hBR hlB)
      · have hjSingleton : j ∈ ({l} : Finset (Fin m)) :=
          (Finset.mem_filter.mp hUHC).2
        have hjEq : j = l := by simpa using hjSingleton
        exact hlj hjEq.symm
    · have hkSingleton : k ∈ ({l} : Finset (Fin m)) :=
        (Finset.mem_filter.mp hUHD).2
      have hkEq : k = l := by simpa using hkSingleton
      exact hlk hkEq.symm
  have hsmallCard : (K ∪ SQ).card + 2 =
      2 * (blockedSignatureSubsetLayer R).card + B.card := by
    rw [Finset.card_union_of_disjoint hKSQ, hKcard, hSQcard]
    omega
  have hsmallSubset : K ∪ SQ ⊆
      rootAndBlockedSignatureSubsetUnion R S := by
    intro U hU
    rcases Finset.mem_union.mp hU with hUK | hUSQ
    · rcases Finset.mem_union.mp hUK with hURC | hUHD
      · rcases Finset.mem_union.mp hURC with hUR | hUHC
        · exact Finset.mem_union_left _ hUR
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨C, hC,
              blockedSignatureContainingSubsetLayer_subset C j hUHC⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨D, hD,
            blockedSignatureContainingSubsetLayer_subset D k hUHD⟩)
    · rcases mem_singletonSubsetFamily_iff.mp hUSQ with ⟨l, hlQ, rfl⟩
      have hlQ' : l ∈ (B.erase j).erase k := by
        simpa [Q] using hlQ
      have hlB : l ∈ B :=
        (Finset.mem_erase.mp (Finset.mem_erase.mp hlQ').2).2
      have hlCover : l ∈ S.biUnion (fun E ↦ B \ E) := by
        rw [hcover]
        exact hlB
      rcases Finset.mem_biUnion.mp hlCover with ⟨E, hE, hlE⟩
      apply Finset.mem_union_right
      apply Finset.mem_biUnion.mpr
      refine ⟨E, hE, ?_⟩
      apply Finset.mem_powerset.mpr
      intro x hx
      have hxl : x = l := by simpa using hx
      subst x
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hlE).2⟩
  calc
    2 * (blockedSignatureSubsetLayer R).card + B.card =
        (K ∪ SQ).card + 2 := hsmallCard.symm
    _ ≤ (rootAndBlockedSignatureSubsetUnion R S).card + 2 :=
      Nat.add_le_add_right (Finset.card_mono hsmallSubset) 2

/-- Union-level form after adjoining the disjoint opposite `B`-face. -/
theorem two_mul_root_add_tailCard_add_tailFace_le_unionWithUpper_add_two
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card + B.card +
        (blockedSignatureSubsetLayer B).card ≤
      (rootAndBlockedSignatureSubsetUnionWithUpper B R S).card + 2 := by
  classical
  have hlower :=
    two_mul_root_add_tailCard_le_covered_signature_union_add_two
      R B S hB hBR hcards hcover hinter
  have hBRinter : (B ∩ R).Nonempty := by
    obtain ⟨j, hjB⟩ := hB
    exact ⟨j, Finset.mem_inter.mpr ⟨hjB, hBR hjB⟩⟩
  rw [card_rootAndBlockedSignatureSubsetUnionWithUpper
    B R S hBRinter hinter]
  omega

/-- Adding the disjoint opposite `B`-face preserves the linear tail surplus. -/
theorem two_mul_root_add_tailCard_add_tailFace_le_fullCube_add_two
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card + B.card +
        (blockedSignatureSubsetLayer B).card ≤ 2 ^ m + 2 := by
  classical
  have henriched :=
    two_mul_root_add_tailCard_add_tailFace_le_unionWithUpper_add_two
      R B S hB hBR hcards hcover hinter
  have hsubset : rootAndBlockedSignatureSubsetUnionWithUpper B R S ⊆
      (Finset.univ : Finset (Fin m)).powerset := by
    intro U _
    exact Finset.mem_powerset.mpr (Finset.subset_univ U)
  have hcube :
      (rootAndBlockedSignatureSubsetUnionWithUpper B R S).card ≤ 2 ^ m := by
    calc
      _ ≤ ((Finset.univ : Finset (Fin m)).powerset).card :=
        Finset.card_mono hsubset
      _ = 2 ^ m := by
        rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  exact henriched.trans (Nat.add_le_add_right hcube 2)

section CollisionTailSurplus

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Numerical full-cube consequence for the actual canonical escape
signature family. -/
theorem two_mul_weight_add_negativeTailCard_add_tailFace_le_fullCube_add_two
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    2 * reducedCollisionWeight (m := m) r + r.val.2.card +
        2 ^ (m - r.val.2.card) ≤ 2 ^ m + 2 := by
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
  have hbound :=
    two_mul_root_add_tailCard_add_tailFace_le_fullCube_add_two
      R r.val.2 S hB hBR hcards hcover' hinter
  have hrootCard : (blockedSignatureSubsetLayer R).card =
      reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  simpa [hrootCard, card_blockedSignatureSubsetLayer] using hbound

/-- Hybrid subset-cube estimate retaining the linear negative-tail surplus.
The additive `2` is the subtraction-free form of `|B_r|-2`. -/
theorem rootWeight_add_negativeTailCard_add_tailUpperCards_le_fullCube_add_contamination_add_two
    {g : Fin (m + 1) → G} {h : G}
    (hh : h + h = 0) (r : ReducedSubsetSumCollision g h)
    (hA : r.val.1.Nonempty)
    (hB : r.val.2.Nonempty)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2)
    (hBinter : ∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.2 ∩ C).Nonempty) :
    (blockedSignatureSubsetLayer (reducedCollisionSupport r)).card +
        r.val.2.card +
        (blockedSignatureUpperSubsetLayer r.val.1).card +
          (blockedSignatureUpperSubsetLayer r.val.2).card ≤
      2 ^ m + (positiveUpperSignatureContamination hh r).card + 2 := by
  classical
  let R := reducedCollisionSupport r
  let S := canonicalSupportEscapeBlockedSignatures hh r
  let E := rootAndBlockedSignatureSubsetUnionWithUpper r.val.2 R S
  let UA := blockedSignatureUpperSubsetLayer r.val.1
  let F := E ∪ UA
  have hBR : r.val.2 ⊆ R := by
    intro j hj
    exact Finset.mem_union_right _ hj
  have hcards : ∀ C ∈ S, C.card = R.card := by
    intro C hC
    exact card_escapeBlockedSignature_eq_rootSupport hh r hrmin hC
  have hcover' : S.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 := by
    change canonicalSupportEscapeBlockedSignatureCoverage hh r = r.val.2
    exact hcover
  have hE : 2 * (blockedSignatureSubsetLayer R).card + r.val.2.card +
      (blockedSignatureSubsetLayer r.val.2).card ≤ E.card + 2 := by
    exact two_mul_root_add_tailCard_add_tailFace_le_unionWithUpper_add_two
      R r.val.2 S hB hBR hcards hcover' hBinter
  have hinter := card_positiveUpper_inter_tailEnriched_le hh r hA
  have hunion := Finset.card_union_add_card_inter E UA
  have hF : F.card ≤ 2 ^ m := by
    have hsubset : F ⊆ (Finset.univ : Finset (Fin m)).powerset := by
      intro V _
      exact Finset.mem_powerset.mpr (Finset.subset_univ V)
    calc
      F.card ≤ ((Finset.univ : Finset (Fin m)).powerset).card :=
        Finset.card_mono hsubset
      _ = 2 ^ m := by
        rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  have hUpperB : (blockedSignatureSubsetLayer r.val.2).card =
      (blockedSignatureUpperSubsetLayer r.val.2).card :=
    (card_blockedSignatureUpperSubsetLayer r.val.2).symm
  rw [hUpperB] at hE
  have hinter' : (E ∩ UA).card ≤
      (positiveUpperSignatureContamination hh r).card +
        (blockedSignatureSubsetLayer R).card := by
    simpa [Finset.inter_comm] using hinter
  have hcardDecomposition : E.card + UA.card =
      F.card + (E ∩ UA).card := by
    simpa only [F] using hunion.symm
  have hcombined : E.card + UA.card ≤
      2 ^ m + ((positiveUpperSignatureContamination hh r).card +
        (blockedSignatureSubsetLayer R).card) := by
    calc
      E.card + UA.card = F.card + (E ∩ UA).card := hcardDecomposition
      _ ≤ 2 ^ m +
          ((positiveUpperSignatureContamination hh r).card +
            (blockedSignatureSubsetLayer R).card) :=
        Nat.add_le_add hF hinter'
  have hmass :
      2 * (blockedSignatureSubsetLayer R).card + r.val.2.card +
          (blockedSignatureUpperSubsetLayer r.val.2).card + UA.card ≤
        E.card + UA.card + 2 := by
    omega
  have htotal := hmass.trans (Nat.add_le_add_right hcombined 2)
  change (blockedSignatureSubsetLayer R).card + r.val.2.card + UA.card +
      (blockedSignatureUpperSubsetLayer r.val.2).card ≤
    2 ^ m + (positiveUpperSignatureContamination hh r).card + 2
  omega

/-- Final strengthened hybrid inequality: the scaled `|B_r|-2` surplus is
retained, while positive-upper contamination is paid by crossing mass. -/
theorem pow_positiveCard_mul_rootWeight_add_negativeTailCard_add_tailUpperCards_le_fullCube_add_crossMass_add_error
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2)
    (hA : r.val.1.Nonempty) :
    2 ^ r.val.1.card *
        (reducedCollisionWeight (m := m) r + r.val.2.card +
          2 ^ (m - r.val.1.card) + 2 ^ (m - r.val.2.card)) ≤
      2 ^ r.val.1.card * 2 ^ m +
        (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
        2 ^ (r.val.1.card + 1) := by
  have hB := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  have hBinter : ∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hcube :=
    rootWeight_add_negativeTailCard_add_tailUpperCards_le_fullCube_add_contamination_add_two
      hh r hA hB hrmin hcover hBinter
  have hcharge := pow_positiveCard_mul_contamination_le_crossMass
    hg hh hh0 r hr hrmin
  have hrootCard :
      (blockedSignatureSubsetLayer (reducedCollisionSupport r)).card =
        reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  have hUpperA :
      (blockedSignatureUpperSubsetLayer r.val.1).card =
        2 ^ (m - r.val.1.card) := by
    rw [card_blockedSignatureUpperSubsetLayer,
      card_blockedSignatureSubsetLayer]
  have hUpperB :
      (blockedSignatureUpperSubsetLayer r.val.2).card =
        2 ^ (m - r.val.2.card) := by
    rw [card_blockedSignatureUpperSubsetLayer,
      card_blockedSignatureSubsetLayer]
  rw [hrootCard, hUpperA, hUpperB] at hcube
  have hscaled := Nat.mul_le_mul_left (2 ^ r.val.1.card) hcube
  calc
    2 ^ r.val.1.card *
        (reducedCollisionWeight (m := m) r + r.val.2.card +
          2 ^ (m - r.val.1.card) + 2 ^ (m - r.val.2.card)) ≤
      2 ^ r.val.1.card *
        (2 ^ m + (positiveUpperSignatureContamination hh r).card + 2) :=
      hscaled
    _ = 2 ^ r.val.1.card * 2 ^ m +
        2 ^ r.val.1.card *
          (positiveUpperSignatureContamination hh r).card +
        2 ^ (r.val.1.card + 1) := by
      rw [pow_succ]
      ring
    _ ≤ 2 ^ r.val.1.card * 2 ^ m +
        (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
        2 ^ (r.val.1.card + 1) :=
      Nat.add_le_add_right
        (Nat.add_le_add_left hcharge (2 ^ r.val.1.card * 2 ^ m)) _

/-- Critical sandwich retaining the scaled linear tail surplus. -/
theorem criticalSmallCrossDominant_tailSurplus_hybrid_sandwich
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hA : r.val.1.Nonempty) :
    4 * (2 ^ r.val.1.card *
        (reducedCollisionWeight (m := n) r + r.val.2.card +
          2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card))) <
      4 * (2 ^ r.val.1.card * 2 ^ n) +
        criticalHalfGap n s * criticalHalfGap n s +
        4 * 2 ^ (r.val.1.card + 1) := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hqodd)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hr' : r ∈ canonicalReducedCollisions (g := g)
      (half_add_half hN) := by
    simpa [criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ u ∈ canonicalReducedCollisions (g := g)
      (half_add_half hN),
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card := by
    simpa [criticalCanonicalReducedCollisions,
      reducedCollisionSupport] using hdominant.2.1
  have hcover : canonicalSupportEscapeBlockedSignatureCoverage
      (half_add_half hN) r = r.val.2 := by
    rcases commonTouched_or_heavy_or_minSupportEscapeIncidences_cover
        g hg (half_add_half hN) (half_ne_zero hN hM) r hr' (by
          simpa [reducedCollisionSupport] using hrmin) with
      htouch | hheavy | hcover
    · exact False.elim (hres.2.1 (by
        simpa [CriticalCommonTouched] using htouch))
    · exact False.elim (hres.2.2 (by
        simpa [CriticalHeavyHalfWitness] using hheavy))
    · exact canonicalSupportEscapeBlockedSignatureCoverage_eq_sourceTail
        (half_add_half hN) r hrmin hcover.1
  have hhybrid :=
    pow_positiveCard_mul_rootWeight_add_negativeTailCard_add_tailUpperCards_le_fullCube_add_crossMass_add_error
      hg (half_add_half hN) (half_ne_zero hN hM) r hr' hrmin hcover hA
  have hhybrid' :
      2 ^ r.val.1.card *
          (reducedCollisionWeight (m := n) r + r.val.2.card +
            2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card)) ≤
        2 ^ r.val.1.card * 2 ^ n + criticalCanonicalCrossMass g +
          2 ^ (r.val.1.card + 1) := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs] using hhybrid
  have hsmall := hres.1.2
  omega

end CollisionTailSurplus

end MinModulus
