/-
# A third tail coordinate forces a fixed fractional surplus

The factor-two signature-union proof chooses two incomparable fibers and
counts two private half-cubes beyond the root.  When the covered tail has a
third coordinate `l`, choose any signature covering it.  Inside that layer,
force `l` present and the two private coordinates absent.  This slice is
disjoint from the root and both private half-cubes, while all other coordinates
remain free.  Its size is at least `2^(padding-3)`.
-/
import MinModulus.G1SignatureTailSlices

namespace MinModulus

open Finset

variable {m : ℕ}

/-- Three distinct coordinates form a three-element finset. -/
theorem card_insert_insert_singleton_eq_three
    {j k l : Fin m} (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ({j, k, l} : Finset (Fin m)).card = 3 := by
  simp [hjk, hjl, hkl]

/-- If at least three tail coordinates are covered, the complete signature
union has a further `2^(padding-3)` elements beyond the factor-two bound. -/
theorem two_mul_root_add_thirdSlice_le_covered_signature_union
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hBcard : 3 ≤ B.card) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        2 ^ (m - R.card - 3) ≤
      (rootAndBlockedSignatureSubsetUnion R S).card := by
  classical
  have hB : B.Nonempty := Finset.card_pos.mp (by omega)
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
  let Q := (B.erase j).erase k
  have hkQ : k ∈ B.erase j := by simp [hkB, hjk.symm]
  have hQcard : Q.card + 2 = B.card := by
    have hkCard := Finset.card_erase_add_one hkQ
    have hjCard := Finset.card_erase_add_one hjB
    change ((B.erase j).erase k).card + 2 = B.card
    omega
  have hQ : Q.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨l, hlQ⟩ := hQ
  have hlQ' : l ∈ (B.erase j).erase k := by simpa [Q] using hlQ
  have hlB : l ∈ B :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hlQ').2).2
  have hlj : l ≠ j :=
    (Finset.mem_erase.mp (Finset.mem_erase.mp hlQ').2).1
  have hlk : l ≠ k := (Finset.mem_erase.mp hlQ').1
  have hlCover : l ∈ S.biUnion (fun E ↦ B \ E) := by
    rw [hcover]
    exact hlB
  rcases Finset.mem_biUnion.mp hlCover with ⟨E, hE, hlE⟩
  let T : Finset (Fin m) := {j, k, l}
  let HC := blockedSignatureContainingSubsetLayer C j
  let HD := blockedSignatureContainingSubsetLayer D k
  let K := (blockedSignatureSubsetLayer R ∪ HC) ∪ HD
  let L := blockedSignatureSingletonTailSlice E T l
  have hTcard : T.card = 3 := by
    exact card_insert_insert_singleton_eq_three hjk hlj.symm hlk.symm
  have hlT : l ∈ T := by simp [T]
  have hlE' : l ∉ E := (Finset.mem_sdiff.mp hlE).2
  have hlTE : l ∈ T \ E := Finset.mem_sdiff.mpr ⟨hlT, hlE'⟩
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
  have hLcard : 2 ^ (m - R.card - 3) ≤ L.card := by
    have hfloor := pow_padding_sub_tailCard_le_singletonTailSlice
      R E T l (hcards E hE) hlT
    simpa [L, hTcard] using hfloor
  have hKL : Disjoint K L := by
    rw [Finset.disjoint_left]
    intro U hUK hUL
    have hInter := inter_tail_eq_singleton_of_mem_singletonTailSlice
      E T l hlTE hUL
    have hlInter : l ∈ U ∩ T := by rw [hInter]; simp
    have hlU := (Finset.mem_inter.mp hlInter).1
    rcases Finset.mem_union.mp hUK with hURC | hUHD
    · rcases Finset.mem_union.mp hURC with hUR | hUHC
      · have hallowed := Finset.mem_powerset.mp hUR
        have hlAllowed := hallowed hlU
        exact (Finset.mem_sdiff.mp hlAllowed).2 (hBR hlB)
      · have hjU : j ∈ U := (Finset.mem_filter.mp hUHC).2
        have hjT : j ∈ T := by simp [T]
        have hjInter : j ∈ U ∩ T :=
          Finset.mem_inter.mpr ⟨hjU, hjT⟩
        have hjSingleton : j ∈ ({l} : Finset (Fin m)) := by
          rw [← hInter]
          exact hjInter
        have hjEq : j = l := by simpa using hjSingleton
        exact hlj hjEq.symm
    · have hkU : k ∈ U := (Finset.mem_filter.mp hUHD).2
      have hkT : k ∈ T := by simp [T]
      have hkInter : k ∈ U ∩ T :=
        Finset.mem_inter.mpr ⟨hkU, hkT⟩
      have hkSingleton : k ∈ ({l} : Finset (Fin m)) := by
        rw [← hInter]
        exact hkInter
      have hkEq : k = l := by simpa using hkSingleton
      exact hlk hkEq.symm
  have hsmallCard :
      2 * (blockedSignatureSubsetLayer R).card +
          2 ^ (m - R.card - 3) ≤ (K ∪ L).card := by
    rw [Finset.card_union_of_disjoint hKL, hKcard]
    exact Nat.add_le_add_left hLcard _
  have hsmallSubset : K ∪ L ⊆
      rootAndBlockedSignatureSubsetUnion R S := by
    intro U hU
    rcases Finset.mem_union.mp hU with hUK | hUL
    · rcases Finset.mem_union.mp hUK with hURC | hUHD
      · rcases Finset.mem_union.mp hURC with hUR | hUHC
        · exact Finset.mem_union_left _ hUR
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨C, hC,
              blockedSignatureContainingSubsetLayer_subset C j hUHC⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨D, hD,
            blockedSignatureContainingSubsetLayer_subset D k hUHD⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨E, hE,
          blockedSignatureSingletonTailSlice_subset E T l hlTE hUL⟩)
  exact hsmallCard.trans (Finset.card_mono hsmallSubset)

/-- Adjoining the disjoint opposite tail face preserves the third-slice
surplus without an additive error term. -/
theorem two_mul_root_add_thirdSlice_add_tailFace_le_unionWithUpper
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hBcard : 3 ≤ B.card) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        2 ^ (m - R.card - 3) +
          (blockedSignatureSubsetLayer B).card ≤
      (rootAndBlockedSignatureSubsetUnionWithUpper B R S).card := by
  classical
  have hlower := two_mul_root_add_thirdSlice_le_covered_signature_union
    R B S hBcard hBR hcards hcover hinter
  have hB : B.Nonempty := Finset.card_pos.mp (by omega)
  have hBRinter : (B ∩ R).Nonempty := by
    obtain ⟨j, hjB⟩ := hB
    exact ⟨j, Finset.mem_inter.mpr ⟨hjB, hBR hjB⟩⟩
  rw [card_rootAndBlockedSignatureSubsetUnionWithUpper
    B R S hBRinter hinter]
  omega

/-- Full Boolean-cube consequence of the third disjoint signature slice. -/
theorem two_mul_root_add_thirdSlice_add_tailFace_le_fullCube
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hBcard : 3 ≤ B.card) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        2 ^ (m - R.card - 3) +
          (blockedSignatureSubsetLayer B).card ≤ 2 ^ m := by
  classical
  have henriched :=
    two_mul_root_add_thirdSlice_add_tailFace_le_unionWithUpper
      R B S hBcard hBR hcards hcover hinter
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
  exact henriched.trans hcube

section CollisionThirdSlice

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Actual collision-family form of the third-slice full-cube estimate. -/
theorem two_mul_weight_add_thirdSlice_add_negativeTailFace_le_fullCube
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2)
    (hBcard : 3 ≤ r.val.2.card) :
    2 * reducedCollisionWeight (m := m) r +
        2 ^ (m - (reducedCollisionSupport r).card - 3) +
          2 ^ (m - r.val.2.card) ≤ 2 ^ m := by
  classical
  let R := reducedCollisionSupport r
  let S := canonicalSupportEscapeBlockedSignatures hh r
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
  have hbound := two_mul_root_add_thirdSlice_add_tailFace_le_fullCube
    R r.val.2 S hBcard hBR hcards hcover' hinter
  have hrootCard : (blockedSignatureSubsetLayer R).card =
      reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  simpa [hrootCard, card_blockedSignatureSubsetLayer] using hbound

/-- Hybrid subset-cube estimate retaining the third-slice surplus.  Unlike
the all-coordinate slice estimate, this fixed fractional gain has no
subtraction error to carry through the positive-face overlap. -/
theorem rootWeight_add_thirdSlice_add_tailUpperCards_le_fullCube_add_contamination
    {g : Fin (m + 1) → G} {h : G}
    (hh : h + h = 0) (r : ReducedSubsetSumCollision g h)
    (hA : r.val.1.Nonempty)
    (hBcard : 3 ≤ r.val.2.card)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2)
    (hBinter : ∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.2 ∩ C).Nonempty) :
    (blockedSignatureSubsetLayer (reducedCollisionSupport r)).card +
        2 ^ (m - (reducedCollisionSupport r).card - 3) +
        (blockedSignatureUpperSubsetLayer r.val.1).card +
          (blockedSignatureUpperSubsetLayer r.val.2).card ≤
      2 ^ m + (positiveUpperSignatureContamination hh r).card := by
  classical
  let R := reducedCollisionSupport r
  let S := canonicalSupportEscapeBlockedSignatures hh r
  let E := rootAndBlockedSignatureSubsetUnionWithUpper r.val.2 R S
  let UA := blockedSignatureUpperSubsetLayer r.val.1
  let F := E ∪ UA
  let t := 2 ^ (m - R.card - 3)
  have hBR : r.val.2 ⊆ R := by
    intro j hj
    exact Finset.mem_union_right _ hj
  have hcards : ∀ C ∈ S, C.card = R.card := by
    intro C hC
    exact card_escapeBlockedSignature_eq_rootSupport hh r hrmin hC
  have hcover' : S.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 := by
    change canonicalSupportEscapeBlockedSignatureCoverage hh r = r.val.2
    exact hcover
  have hE : 2 * (blockedSignatureSubsetLayer R).card + t +
      (blockedSignatureSubsetLayer r.val.2).card ≤ E.card := by
    exact two_mul_root_add_thirdSlice_add_tailFace_le_unionWithUpper
      R r.val.2 S hBcard hBR hcards hcover' hBinter
  have hAinter := card_positiveUpper_inter_tailEnriched_le hh r hA
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
    simpa [Finset.inter_comm] using hAinter
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
      2 * (blockedSignatureSubsetLayer R).card + t +
          (blockedSignatureUpperSubsetLayer r.val.2).card + UA.card ≤
        E.card + UA.card := by
    exact Nat.add_le_add_right hE UA.card
  have htotal := hmass.trans hcombined
  change (blockedSignatureSubsetLayer R).card + t + UA.card +
      (blockedSignatureUpperSubsetLayer r.val.2).card ≤
    2 ^ m + (positiveUpperSignatureContamination hh r).card
  omega

/-- Scaled hybrid crossing inequality with the third-slice surplus surviving
on the left-hand side. -/
theorem pow_positiveCard_mul_rootWeight_add_thirdSlice_add_tailUpperCards_le_fullCube_add_crossMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2)
    (hA : r.val.1.Nonempty)
    (hBcard : 3 ≤ r.val.2.card) :
    let t := 2 ^ (m - (reducedCollisionSupport r).card - 3)
    2 ^ r.val.1.card *
        (reducedCollisionWeight (m := m) r + t +
          2 ^ (m - r.val.1.card) + 2 ^ (m - r.val.2.card)) ≤
      2 ^ r.val.1.card * 2 ^ m +
        (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) := by
  dsimp only
  have hB : r.val.2.Nonempty := Finset.card_pos.mp (by omega)
  have hBinter : ∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hcube :=
    rootWeight_add_thirdSlice_add_tailUpperCards_le_fullCube_add_contamination
      hh r hA hBcard hrmin hcover hBinter
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
    _ ≤ 2 ^ r.val.1.card *
        (2 ^ m + (positiveUpperSignatureContamination hh r).card) := hscaled
    _ = 2 ^ r.val.1.card * 2 ^ m +
        2 ^ r.val.1.card *
          (positiveUpperSignatureContamination hh r).card := by ring
    _ ≤ _ := Nat.add_le_add_left hcharge _

/-- In a genuine dominant residual with at least three negative-tail
coordinates, the third-slice term is exactly one eighth of the root weight.
The universal fiber bound supplies the otherwise necessary three padding
coordinates. -/
theorem eight_mul_thirdSlice_eq_weight_of_genuineDominant
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : 3 ≤ r.val.2.card) :
    8 * 2 ^ (n - (reducedCollisionSupport r).card - 3) =
      reducedCollisionWeight (m := n) r := by
  have htailWeight := two_mul_negativeTailCard_lt_weight_of_genuineDominant
    hqodd g hg r hr hres
  have hsix : 6 ≤ 2 * r.val.2.card := by omega
  have hweightDef : reducedCollisionWeight (m := n) r =
      2 ^ (n - (reducedCollisionSupport r).card) := by
    rfl
  rw [hweightDef] at htailWeight
  have hsixPow : 6 < 2 ^ (n - (reducedCollisionSupport r).card) := by
    exact hsix.trans_lt htailWeight
  have hfourPow : 2 ^ 2 < 2 ^ (n - (reducedCollisionSupport r).card) := by
    calc
      2 ^ 2 = 4 := by norm_num
      _ < 6 := by norm_num
      _ < _ := hsixPow
  have hpadding : 3 ≤ n - (reducedCollisionSupport r).card := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hfourPow
    omega
  calc
    8 * 2 ^ (n - (reducedCollisionSupport r).card - 3) =
        2 ^ 3 * 2 ^ (n - (reducedCollisionSupport r).card - 3) := by
      norm_num
    _ = 2 ^ (3 + (n - (reducedCollisionSupport r).card - 3)) := by
      exact (pow_add (2 : ℕ) 3
        (n - (reducedCollisionSupport r).card - 3)).symm
    _ = 2 ^ (n - (reducedCollisionSupport r).card) := by
      congr 1
      omega
    _ = reducedCollisionWeight (m := n) r := rfl

/-- Critical small-crossing sandwich with a fixed third-slice surplus and no
right-hand error term. -/
theorem criticalSmallCrossDominant_thirdSlice_hybrid_sandwich
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hA : r.val.1.Nonempty)
    (hBcard : 3 ≤ r.val.2.card) :
    let t := 2 ^ (n - (reducedCollisionSupport r).card - 3)
    4 * (2 ^ r.val.1.card *
        (reducedCollisionWeight (m := n) r + t +
          2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card))) <
      4 * (2 ^ r.val.1.card * 2 ^ n) +
        criticalHalfGap n s * criticalHalfGap n s := by
  classical
  dsimp only
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
    pow_positiveCard_mul_rootWeight_add_thirdSlice_add_tailUpperCards_le_fullCube_add_crossMass
      hg (half_add_half hN) (half_ne_zero hN hM) r hr' hrmin hcover hA hBcard
  have hhybrid' :
      2 ^ r.val.1.card *
          (reducedCollisionWeight (m := n) r +
            2 ^ (n - (reducedCollisionSupport r).card - 3) +
            2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card)) ≤
        2 ^ r.val.1.card * 2 ^ n + criticalCanonicalCrossMass g := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs] using hhybrid
  have hsmall := hres.1.2
  omega

end CollisionThirdSlice

end MinModulus
