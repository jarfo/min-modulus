/-
# Hybrid upper-face and crossing-mass bound

The positive-tail upper face is obstructed precisely by signature layers whose
blocked sets avoid the positive tail.  This file measures each obstruction
exactly and combines their total with the crossing-mass charge.

For disjoint coordinate sets `T,C`, the intersection of the upper face forcing
`T` and the lower face avoiding `C` has codimension `|T|` inside the lower
face.  Thus scaling its cardinality by `2^|T|` recovers one full signature
layer.  Summed over all `A_r`-avoiding signatures, the scaled contamination is
exactly their number times `w_r`, hence is paid for by canonical crossing
mass.
-/
import MinModulus.G1SignatureCrossingCharge

namespace MinModulus

open Finset

section UpperLowerIntersection

variable {m : ℕ}

/-- Exact size of the intersection between an upper face forcing `T` and a
lower signature face avoiding a disjoint `C`. -/
theorem card_upperSubsetLayer_inter_blockedSubsetLayer
    (T C : Finset (Fin m)) (hTC : Disjoint T C) :
    (blockedSignatureUpperSubsetLayer T ∩
        blockedSignatureSubsetLayer C).card =
      2 ^ (m - (T ∪ C).card) := by
  classical
  let F := Finset.univ \ (T ∪ C)
  have hcard : F.powerset.card =
      (blockedSignatureUpperSubsetLayer T ∩
        blockedSignatureSubsetLayer C).card := by
    apply Finset.card_bij (fun W _ ↦ T ∪ W)
    · intro W hW
      have hWsub := Finset.mem_powerset.mp hW
      apply Finset.mem_inter.mpr
      constructor
      · exact mem_blockedSignatureUpperSubsetLayer_iff.mpr
          Finset.subset_union_left
      · rw [blockedSignatureSubsetLayer, Finset.mem_powerset]
        intro j hj
        rcases Finset.mem_union.mp hj with hjT | hjW
        · exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ _, Finset.disjoint_left.mp hTC hjT⟩
        · have hjF := Finset.mem_sdiff.mp (hWsub hjW)
          exact Finset.mem_sdiff.mpr
            ⟨Finset.mem_univ _, fun hjC ↦
              hjF.2 (Finset.mem_union_right _ hjC)⟩
    · intro W hW V hV hWV
      have hWsub := Finset.mem_powerset.mp hW
      have hVsub := Finset.mem_powerset.mp hV
      have hTW : Disjoint T W := by
        rw [Finset.disjoint_left]
        intro j hjT hjW
        exact (Finset.mem_sdiff.mp (hWsub hjW)).2
          (Finset.mem_union_left _ hjT)
      have hTV : Disjoint T V := by
        rw [Finset.disjoint_left]
        intro j hjT hjV
        exact (Finset.mem_sdiff.mp (hVsub hjV)).2
          (Finset.mem_union_left _ hjT)
      calc
        W = (T ∪ W) \ T := (Finset.union_sdiff_cancel_left hTW).symm
        _ = (T ∪ V) \ T := by rw [hWV]
        _ = V := Finset.union_sdiff_cancel_left hTV
    · intro V hV
      have hVUpper := (Finset.mem_inter.mp hV).1
      have hVLower := (Finset.mem_inter.mp hV).2
      refine ⟨V \ T, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro j hj
        have hj' := Finset.mem_sdiff.mp hj
        have hVallowed := Finset.mem_powerset.mp hVLower
        have hjAllowed := Finset.mem_sdiff.mp (hVallowed hj'.1)
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, fun hjTC ↦ by
            rcases Finset.mem_union.mp hjTC with hjT | hjC
            · exact hj'.2 hjT
            · exact hjAllowed.2 hjC⟩
      · exact Finset.union_sdiff_of_subset
          (mem_blockedSignatureUpperSubsetLayer_iff.mp hVUpper)
  dsimp only [F] at hcard
  rw [← hcard, Finset.card_powerset,
    Finset.card_sdiff_of_subset (Finset.subset_univ (T ∪ C)),
    Finset.card_univ, Fintype.card_fin]

/-- Scaling the obstruction by the forced-face dimension recovers the full
lower signature layer. -/
theorem pow_card_mul_card_upper_inter_blocked_eq_blocked
    (T C : Finset (Fin m)) (hTC : Disjoint T C) :
    2 ^ T.card *
        (blockedSignatureUpperSubsetLayer T ∩
          blockedSignatureSubsetLayer C).card =
      (blockedSignatureSubsetLayer C).card := by
  have hcardUnion : (T ∪ C).card = T.card + C.card :=
    Finset.card_union_of_disjoint hTC
  have hsumle : T.card + C.card ≤ m := by
    rw [← hcardUnion]
    simpa using Finset.card_le_univ (T ∪ C)
  rw [card_upperSubsetLayer_inter_blockedSubsetLayer T C hTC,
    card_blockedSignatureSubsetLayer, ← pow_add, hcardUnion]
  congr 1
  omega

end UpperLowerIntersection

section SignatureContamination

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Portion of the positive-tail upper face covered by at least one
positive-tail-avoiding signature layer. -/
noncomputable def positiveUpperSignatureContamination
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset (Finset (Fin m)) := by
  classical
  exact (positiveTailAvoidingEscapeBlockedSignatures hh r).biUnion (fun C ↦
    blockedSignatureUpperSubsetLayer r.val.1 ∩
      blockedSignatureSubsetLayer C)

/-- After scaling by `2^|A_r|`, total positive-upper contamination is at
most the number of avoiding signatures times one dominant weight. -/
theorem pow_positiveCard_mul_contamination_le_avoidingCard_mul_weight
    {g : Fin (m + 1) → G} {h : G}
    (hh : h + h = 0) (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card) :
    2 ^ r.val.1.card * (positiveUpperSignatureContamination hh r).card ≤
      (positiveTailAvoidingEscapeBlockedSignatures hh r).card *
        reducedCollisionWeight (m := m) r := by
  classical
  let S₀ := positiveTailAvoidingEscapeBlockedSignatures hh r
  let I : Finset (Fin m) → Finset (Finset (Fin m)) := fun C ↦
    blockedSignatureUpperSubsetLayer r.val.1 ∩
      blockedSignatureSubsetLayer C
  have hcardUnion : (positiveUpperSignatureContamination hh r).card ≤
      S₀.sum (fun C ↦ (I C).card) := by
    exact Finset.card_biUnion_le
  have hscaled : ∀ C ∈ S₀,
      2 ^ r.val.1.card * (I C).card =
        reducedCollisionWeight (m := m) r := by
    intro C hC
    have hC' := mem_positiveTailAvoidingEscapeBlockedSignatures_iff.mp hC
    have hdisj : Disjoint r.val.1 C := by
      rw [Finset.disjoint_iff_inter_eq_empty]
      exact hC'.2
    calc
      2 ^ r.val.1.card * (I C).card =
          (blockedSignatureSubsetLayer C).card :=
        pow_card_mul_card_upper_inter_blocked_eq_blocked r.val.1 C hdisj
      _ = reducedCollisionWeight (m := m) r := by
        rw [card_blockedSignatureSubsetLayer,
          card_escapeBlockedSignature_eq_rootSupport hh r hrmin hC'.1]
        rfl
  calc
    2 ^ r.val.1.card * (positiveUpperSignatureContamination hh r).card ≤
        2 ^ r.val.1.card * S₀.sum (fun C ↦ (I C).card) :=
      Nat.mul_le_mul_left _ hcardUnion
    _ = S₀.sum (fun C ↦ 2 ^ r.val.1.card * (I C).card) := by
      rw [Finset.mul_sum]
    _ = S₀.sum (fun _ ↦ reducedCollisionWeight (m := m) r) := by
      apply Finset.sum_congr rfl
      intro C hC
      exact hscaled C hC
    _ = S₀.card * reducedCollisionWeight (m := m) r := by simp

/-- Combining the contamination estimate with the reverse-crossing charge. -/
theorem pow_positiveCard_mul_contamination_le_crossMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card) :
    2 ^ r.val.1.card * (positiveUpperSignatureContamination hh r).card ≤
      (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  exact (pow_positiveCard_mul_contamination_le_avoidingCard_mul_weight
    hh r hrmin).trans
      (avoidingSignatureCard_mul_weight_le_crossMass
        hg hh hh0 r hr hrmin)

/-- When the source positive tail is nonempty, its upper face meets the lower
root/signature union only through the explicitly recorded avoiding-signature
contamination. -/
theorem positiveUpper_inter_rootAndSignatureUnion_subset_contamination
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) (hA : r.val.1.Nonempty) :
    blockedSignatureUpperSubsetLayer r.val.1 ∩
        rootAndBlockedSignatureSubsetUnion (reducedCollisionSupport r)
          (canonicalSupportEscapeBlockedSignatures hh r) ⊆
      positiveUpperSignatureContamination hh r := by
  classical
  intro V hV
  have hUpper := (Finset.mem_inter.mp hV).1
  have hLower := (Finset.mem_inter.mp hV).2
  rcases Finset.mem_union.mp hLower with hRoot | hFamily
  · obtain ⟨j, hjA⟩ := hA
    have hjV := (mem_blockedSignatureUpperSubsetLayer_iff.mp hUpper) hjA
    have hVroot := Finset.mem_powerset.mp hRoot
    have hjAllowed := Finset.mem_sdiff.mp (hVroot hjV)
    exact False.elim (hjAllowed.2 (Finset.mem_union_left _ hjA))
  · rcases Finset.mem_biUnion.mp hFamily with ⟨C, hC, hVC⟩
    by_cases hAC : r.val.1 ∩ C = ∅
    · apply Finset.mem_biUnion.mpr
      refine ⟨C,
        mem_positiveTailAvoidingEscapeBlockedSignatures_iff.mpr ⟨hC, hAC⟩,
        Finset.mem_inter.mpr ⟨hUpper, hVC⟩⟩
    · have hACne : (r.val.1 ∩ C).Nonempty :=
        Finset.nonempty_iff_ne_empty.mpr hAC
      obtain ⟨j, hj⟩ := hACne
      have hjA := (Finset.mem_inter.mp hj).1
      have hjC := (Finset.mem_inter.mp hj).2
      have hjV := (mem_blockedSignatureUpperSubsetLayer_iff.mp hUpper) hjA
      have hVallowed := Finset.mem_powerset.mp hVC
      exact False.elim ((Finset.mem_sdiff.mp (hVallowed hjV)).2 hjC)

/-- The positive upper face intersects the negative-tail-enriched union by at
most its signature contamination plus the full-root upper face. -/
theorem card_positiveUpper_inter_tailEnriched_le
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) (hA : r.val.1.Nonempty) :
    (blockedSignatureUpperSubsetLayer r.val.1 ∩
        rootAndBlockedSignatureSubsetUnionWithUpper r.val.2
          (reducedCollisionSupport r)
          (canonicalSupportEscapeBlockedSignatures hh r)).card ≤
      (positiveUpperSignatureContamination hh r).card +
        (blockedSignatureSubsetLayer (reducedCollisionSupport r)).card := by
  classical
  let L := rootAndBlockedSignatureSubsetUnion (reducedCollisionSupport r)
    (canonicalSupportEscapeBlockedSignatures hh r)
  let UA := blockedSignatureUpperSubsetLayer r.val.1
  let UB := blockedSignatureUpperSubsetLayer r.val.2
  let J := positiveUpperSignatureContamination hh r
  have hsubset : UA ∩ (L ∪ UB) ⊆ J ∪ (UA ∩ UB) := by
    intro V hV
    have hVA := (Finset.mem_inter.mp hV).1
    rcases Finset.mem_union.mp (Finset.mem_inter.mp hV).2 with hVL | hVUB
    · exact Finset.mem_union_left _
        (positiveUpper_inter_rootAndSignatureUnion_subset_contamination
          hh r hA (Finset.mem_inter.mpr ⟨hVA, hVL⟩))
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hVA, hVUB⟩)
  have hcard := (Finset.card_mono hsubset).trans (Finset.card_union_le J (UA ∩ UB))
  have hinter : UA ∩ UB =
      blockedSignatureUpperSubsetLayer (reducedCollisionSupport r) := by
    rw [blockedSignatureUpperSubsetLayers_inter]
    rfl
  rw [rootAndBlockedSignatureSubsetUnionWithUpper]
  change (UA ∩ (L ∪ UB)).card ≤ _
  rw [hinter] at hcard
  simpa [J, card_blockedSignatureUpperSubsetLayer] using hcard

/-- Hybrid subset-cube estimate: after adding the positive upper face, its
only loss beyond the exact lower/tail-face mass is recorded contamination. -/
theorem rootWeight_add_tailUpperCards_le_fullCube_add_contamination
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
        (blockedSignatureUpperSubsetLayer r.val.1).card +
          (blockedSignatureUpperSubsetLayer r.val.2).card ≤
      2 ^ m + (positiveUpperSignatureContamination hh r).card := by
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
  have hE : 2 * (blockedSignatureSubsetLayer R).card +
      (blockedSignatureSubsetLayer r.val.2).card ≤ E.card := by
    exact two_mul_root_add_tailFace_le_unionWithUpper_of_inter_nonempty
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
      2 * (blockedSignatureSubsetLayer R).card +
          (blockedSignatureUpperSubsetLayer r.val.2).card + UA.card ≤
        E.card + UA.card :=
    Nat.add_le_add_right hE UA.card
  have htotal := hmass.trans hcombined
  change (blockedSignatureSubsetLayer R).card + UA.card +
      (blockedSignatureUpperSubsetLayer r.val.2).card ≤
    2 ^ m + (positiveUpperSignatureContamination hh r).card
  omega

/-- Final hybrid inequality: scaled positive-upper contamination is paid by
canonical crossing mass. -/
theorem pow_positiveCard_mul_rootWeight_add_tailUpperCards_le_fullCube_add_crossMass
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
        (reducedCollisionWeight (m := m) r +
          2 ^ (m - r.val.1.card) + 2 ^ (m - r.val.2.card)) ≤
      2 ^ r.val.1.card * 2 ^ m +
        (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) := by
  have hB := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  have hBinter : ∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hcube := rootWeight_add_tailUpperCards_le_fullCube_add_contamination
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
  calc
    2 ^ r.val.1.card *
        (reducedCollisionWeight (m := m) r +
          2 ^ (m - r.val.1.card) + 2 ^ (m - r.val.2.card)) ≤
      2 ^ r.val.1.card *
        (2 ^ m + (positiveUpperSignatureContamination hh r).card) :=
      Nat.mul_le_mul_left _ hcube
    _ = 2 ^ r.val.1.card * 2 ^ m +
        2 ^ r.val.1.card *
          (positiveUpperSignatureContamination hh r).card := by
      rw [Nat.mul_add]
    _ ≤ 2 ^ r.val.1.card * 2 ^ m +
        (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) :=
      Nat.add_le_add_left hcharge _

end SignatureContamination

end MinModulus
