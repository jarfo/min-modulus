/-
# Fiber-adaptive signature slices

Uniform tail-slice bounds replace every realizing signature fiber by the
whole source tail.  This can lose an exponential factor.  For each covered
coordinate, select one realizing signature and retain the exact cardinality
of its singleton-tail slice:

`2^(m-|C union B|) = 2^(padding-|B\C|)`.

Slices chosen for distinct coordinates remain disjoint because their
intersection with `B` is a different singleton.  The resulting sum records
the actual blocked-signature fiber sizes and can grow linearly in the number
of singleton fibers.
-/
import MinModulus.G1MeetingOrderedSlices

namespace MinModulus

open Finset

variable {m : ℕ}

/-- A canonical minimum-fiber signature covering `j`, with the empty set as
an irrelevant fallback when no such signature exists.  The finite minimum
is taken with respect to `|(B \ C)|`; ties are resolved by classical choice. -/
noncomputable def selectedCoveringSignature
    (S : Finset (Finset (Fin m))) (B : Finset (Fin m)) (j : Fin m) :
    Finset (Fin m) := by
  classical
  let T := S.filter (fun C ↦ j ∈ B \ C)
  exact if hT : T.Nonempty then
    Classical.choose (T.exists_min_image (fun C ↦ (B \ C).card) hT)
  else ∅

theorem selectedCoveringSignature_mem_and_covers
    (S : Finset (Finset (Fin m))) (B : Finset (Fin m)) (j : Fin m)
    (h : ∃ C ∈ S, j ∈ B \ C) :
    selectedCoveringSignature S B j ∈ S ∧
      j ∈ B \ selectedCoveringSignature S B j := by
  classical
  let T := S.filter (fun C ↦ j ∈ B \ C)
  have hT : T.Nonempty := by
    rcases h with ⟨C, hCS, hjC⟩
    exact ⟨C, Finset.mem_filter.mpr ⟨hCS, hjC⟩⟩
  rw [selectedCoveringSignature, dif_pos hT]
  exact (Finset.mem_filter.mp
    (Classical.choose_spec
      (T.exists_min_image (fun C ↦ (B \ C).card) hT)).1)

/-- The selected covering signature has the smallest escape fiber among all
signatures covering the same coordinate. -/
theorem selectedCoveringSignature_fiberCard_le
    (S : Finset (Finset (Fin m))) (B : Finset (Fin m)) (j : Fin m)
    (h : ∃ C ∈ S, j ∈ B \ C)
    {C : Finset (Fin m)} (hCS : C ∈ S) (hjC : j ∈ B \ C) :
    (B \ selectedCoveringSignature S B j).card ≤ (B \ C).card := by
  classical
  let T := S.filter (fun D ↦ j ∈ B \ D)
  have hT : T.Nonempty := by
    rcases h with ⟨D, hDS, hjD⟩
    exact ⟨D, Finset.mem_filter.mpr ⟨hDS, hjD⟩⟩
  have hCT : C ∈ T := Finset.mem_filter.mpr ⟨hCS, hjC⟩
  rw [selectedCoveringSignature, dif_pos hT]
  exact (Classical.choose_spec
    (T.exists_min_image (fun D ↦ (B \ D).card) hT)).2 C hCT

/-- Full coverage supplies the selected signature at every coordinate. -/
theorem selectedCoveringSignature_mem_and_covers_of_biUnion_eq
    (S : Finset (Finset (Fin m))) (B : Finset (Fin m))
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    {j : Fin m} (hjB : j ∈ B) :
    selectedCoveringSignature S B j ∈ S ∧
      j ∈ B \ selectedCoveringSignature S B j := by
  classical
  have hjCover : j ∈ S.biUnion (fun C ↦ B \ C) := by
    rw [hcover]
    exact hjB
  rcases Finset.mem_biUnion.mp hjCover with ⟨C, hC, hjC⟩
  exact selectedCoveringSignature_mem_and_covers S B j ⟨C, hC, hjC⟩

/-- The exact singleton-tail slice selected at coordinate `j`. -/
noncomputable def selectedFiberTailSliceAt
    (S : Finset (Finset (Fin m))) (B : Finset (Fin m)) (j : Fin m) :
    Finset (Finset (Fin m)) :=
  blockedSignatureSingletonTailSlice (selectedCoveringSignature S B j) B j

/-- Union of selected exact-fiber slices over a coordinate set `Q`. -/
noncomputable def selectedFiberTailSlices
    (S : Finset (Finset (Fin m))) (B Q : Finset (Fin m)) :
    Finset (Finset (Fin m)) := by
  classical
  exact Q.biUnion (selectedFiberTailSliceAt S B)

/-- Sum of the exact selected slice cardinalities. -/
noncomputable def selectedFiberSliceMass
    (S : Finset (Finset (Fin m))) (B Q : Finset (Fin m)) : ℕ :=
  ∑ j ∈ Q, 2 ^
    (m - ((selectedCoveringSignature S B j) ∪ B).card)

/-- Selected slices at distinct covered coordinates are disjoint. -/
theorem selectedFiberTailSliceAt_disjoint
    (S : Finset (Finset (Fin m))) (B : Finset (Fin m))
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    {j k : Fin m} (hjB : j ∈ B) (hkB : k ∈ B) (hjk : j ≠ k) :
    Disjoint (selectedFiberTailSliceAt S B j)
      (selectedFiberTailSliceAt S B k) := by
  classical
  have hj := (selectedCoveringSignature_mem_and_covers_of_biUnion_eq
    S B hcover hjB).2
  have hk := (selectedCoveringSignature_mem_and_covers_of_biUnion_eq
    S B hcover hkB).2
  exact blockedSignatureSingletonTailSlices_disjoint
    (selectedCoveringSignature S B j)
    (selectedCoveringSignature S B k) B j k hj hk hjk

/-- The selected slice union has exactly the fiber-adaptive mass. -/
theorem card_selectedFiberTailSlices
    (S : Finset (Finset (Fin m))) (B Q : Finset (Fin m))
    (hQB : Q ⊆ B)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    (selectedFiberTailSlices S B Q).card =
      selectedFiberSliceMass S B Q := by
  classical
  have hpairwise : (Q : Set (Fin m)).PairwiseDisjoint
      (selectedFiberTailSliceAt S B) := by
    intro j hjQ k hkQ hjk
    exact selectedFiberTailSliceAt_disjoint S B hcover
      (hQB hjQ) (hQB hkQ) hjk
  rw [selectedFiberTailSlices, Finset.card_biUnion hpairwise,
    selectedFiberSliceMass]
  apply Finset.sum_congr rfl
  intro j hjQ
  exact card_blockedSignatureSingletonTailSlice
    (selectedCoveringSignature S B j) B j (hQB hjQ)

/-- Every selected slice lies in its selected realized signature layer. -/
theorem selectedFiberTailSlices_subset_rootAndSignatureUnion
    (R : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (B Q : Finset (Fin m))
    (hQB : Q ⊆ B)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    selectedFiberTailSlices S B Q ⊆
      rootAndBlockedSignatureSubsetUnion R S := by
  classical
  intro U hU
  rcases Finset.mem_biUnion.mp hU with ⟨j, hjQ, hUj⟩
  have hj := selectedCoveringSignature_mem_and_covers_of_biUnion_eq
    S B hcover (hQB hjQ)
  exact Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨selectedCoveringSignature S B j, hj.1,
      blockedSignatureSingletonTailSlice_subset
        (selectedCoveringSignature S B j) B j hj.2 hUj⟩)

/-- The root padding layer is disjoint from all selected slices because each
slice contains its selected coordinate in `B ⊆ R`. -/
theorem blockedSignatureSubsetLayer_disjoint_selectedFiberTailSlices
    (R : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (B Q : Finset (Fin m))
    (hQB : Q ⊆ B) (hBR : B ⊆ R)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    Disjoint (blockedSignatureSubsetLayer R)
      (selectedFiberTailSlices S B Q) := by
  classical
  rw [Finset.disjoint_left]
  intro U hUR hUS
  rcases Finset.mem_biUnion.mp hUS with ⟨j, hjQ, hUj⟩
  have hjB := hQB hjQ
  have hjCover := (selectedCoveringSignature_mem_and_covers_of_biUnion_eq
    S B hcover hjB).2
  have hInter := inter_tail_eq_singleton_of_mem_singletonTailSlice
    (selectedCoveringSignature S B j) B j hjCover hUj
  have hjInter : j ∈ U ∩ B := by rw [hInter]; simp
  have hjU := (Finset.mem_inter.mp hjInter).1
  have hjAllowed := Finset.mem_powerset.mp hUR hjU
  exact (Finset.mem_sdiff.mp hjAllowed).2 (hBR hjB)

/-- Root plus all selected exact-fiber slices gives an additive
fiber-adaptive lower bound for the complete signature union. -/
theorem root_add_selectedFiberSliceMass_le_rootAndSignatureUnion
    (R : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (B Q : Finset (Fin m))
    (hQB : Q ⊆ B) (hBR : B ⊆ R)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    (blockedSignatureSubsetLayer R).card +
        selectedFiberSliceMass S B Q ≤
      (rootAndBlockedSignatureSubsetUnion R S).card := by
  classical
  let O := selectedFiberTailSlices S B Q
  have hdisj := blockedSignatureSubsetLayer_disjoint_selectedFiberTailSlices
    R S B Q hQB hBR hcover
  have hcard : (blockedSignatureSubsetLayer R ∪ O).card =
      (blockedSignatureSubsetLayer R).card +
        selectedFiberSliceMass S B Q := by
    rw [Finset.card_union_of_disjoint hdisj,
      show O.card = selectedFiberSliceMass S B Q by
        simpa [O] using card_selectedFiberTailSlices S B Q hQB hcover]
  have hsubset : blockedSignatureSubsetLayer R ∪ O ⊆
      rootAndBlockedSignatureSubsetUnion R S := by
    intro U hU
    rcases Finset.mem_union.mp hU with hUR | hUO
    · exact Finset.mem_union_left _ hUR
    · exact selectedFiberTailSlices_subset_rootAndSignatureUnion
        R S B Q hQB hcover hUO
  rw [← hcard]
  exact Finset.card_mono hsubset

/-- Equal signature/root cardinalities rewrite a selected slice exactly in
terms of the actual omitted fiber `B\C`. -/
theorem selectedFiberSliceWeight_eq_pow_padding_sub_fiberCard
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    {j : Fin m} (hjB : j ∈ B) :
    2 ^ (m - ((selectedCoveringSignature S B j) ∪ B).card) =
      2 ^ (m - R.card -
        (B \ selectedCoveringSignature S B j).card) := by
  classical
  have hj := selectedCoveringSignature_mem_and_covers_of_biUnion_eq
    S B hcover hjB
  have hCcard := hcards (selectedCoveringSignature S B j) hj.1
  have hunion : ((selectedCoveringSignature S B j) ∪ B).card =
      (selectedCoveringSignature S B j).card +
        (B \ selectedCoveringSignature S B j).card := by
    have hinterle :
        (B ∩ selectedCoveringSignature S B j).card ≤ B.card :=
      Finset.card_le_card Finset.inter_subset_left
    rw [Finset.card_union, Finset.card_sdiff]
    rw [Finset.inter_comm (selectedCoveringSignature S B j) B]
    omega
  rw [hunion, hCcard]
  congr 1
  omega

/-- Whole-tail form of the exact padding-minus-fiber normalization. -/
theorem selectedFiberSliceMass_eq_sum_pow_padding_sub_fiberCard
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    selectedFiberSliceMass S B B =
      ∑ j ∈ B, 2 ^ (m - R.card -
        (B \ selectedCoveringSignature S B j).card) := by
  classical
  rw [selectedFiberSliceMass]
  apply Finset.sum_congr rfl
  intro j hjB
  exact selectedFiberSliceWeight_eq_pow_padding_sub_fiberCard
    R B S hcards hcover hjB

/-- The opposite tail upper face is disjoint from the root and every selected
signature slice.  Hence the exact fiber-adaptive mass survives in the full
Boolean-cube bound. -/
theorem root_add_selectedFiberSliceMass_add_tailFace_le_fullCube
    (R : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (B Q : Finset (Fin m))
    (hB : B.Nonempty) (hQB : Q ⊆ B) (hBR : B ⊆ R)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hBmeet : ∀ C ∈ S, (B ∩ C).Nonempty) :
    (blockedSignatureSubsetLayer R).card +
        selectedFiberSliceMass S B Q +
          (blockedSignatureUpperSubsetLayer B).card ≤ 2 ^ m := by
  classical
  let Root := blockedSignatureSubsetLayer R
  let O := selectedFiberTailSlices S B Q
  let L := Root ∪ O
  let Upper := blockedSignatureUpperSubsetLayer B
  let F := L ∪ Upper
  have hRootO : Disjoint Root O :=
    blockedSignatureSubsetLayer_disjoint_selectedFiberTailSlices
      R S B Q hQB hBR hcover
  have hLcard : L.card = Root.card + O.card :=
    Finset.card_union_of_disjoint hRootO
  have hLsub : L ⊆ rootAndBlockedSignatureSubsetUnion R S := by
    intro U hU
    rcases Finset.mem_union.mp hU with hUR | hUO
    · exact Finset.mem_union_left _ hUR
    · exact selectedFiberTailSlices_subset_rootAndSignatureUnion
        R S B Q hQB hcover hUO
  have hBRinter : (B ∩ R).Nonempty := by
    obtain ⟨j, hjB⟩ := hB
    exact ⟨j, Finset.mem_inter.mpr ⟨hjB, hBR hjB⟩⟩
  have hUpperLower : Disjoint Upper
      (rootAndBlockedSignatureSubsetUnion R S) := by
    exact blockedSignatureUpperSubsetLayer_disjoint_rootAndUnion
      B R S hBRinter hBmeet
  have hLUpper : Disjoint L Upper :=
    (hUpperLower.mono_right hLsub).symm
  have hFcard : F.card = L.card + Upper.card :=
    Finset.card_union_of_disjoint hLUpper
  have hOcard : O.card = selectedFiberSliceMass S B Q := by
    simpa [O] using card_selectedFiberTailSlices S B Q hQB hcover
  have hFcube : F.card ≤ 2 ^ m := by
    have hsubset : F ⊆ (Finset.univ : Finset (Fin m)).powerset := by
      intro U _
      exact Finset.mem_powerset.mpr (Finset.subset_univ U)
    calc
      F.card ≤ ((Finset.univ : Finset (Fin m)).powerset).card :=
        Finset.card_mono hsubset
      _ = 2 ^ m := by
        rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]
  change Root.card + selectedFiberSliceMass S B Q + Upper.card ≤ 2 ^ m
  omega

section CollisionFiberAdaptiveSlices

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Actual collision form of the exact fiber-adaptive tail-face bound. -/
theorem weight_add_selectedFiberSliceMass_add_negativeTailFace_le_fullCube
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    let S := canonicalSupportEscapeBlockedSignatures hh r
    reducedCollisionWeight (m := m) r +
        selectedFiberSliceMass S r.val.2 r.val.2 +
          2 ^ (m - r.val.2.card) ≤ 2 ^ m := by
  classical
  dsimp only
  let R := reducedCollisionSupport r
  let S := canonicalSupportEscapeBlockedSignatures hh r
  have hB := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  have hBR : r.val.2 ⊆ R := by
    intro j hj
    exact Finset.mem_union_right _ hj
  have hcover' : S.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 := by
    change canonicalSupportEscapeBlockedSignatureCoverage hh r = r.val.2
    exact hcover
  have hBmeet : ∀ C ∈ S, (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hbound := root_add_selectedFiberSliceMass_add_tailFace_le_fullCube
    R S r.val.2 r.val.2 hB (by rfl) hBR hcover' hBmeet
  have hrootCard : (blockedSignatureSubsetLayer R).card =
      reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  rw [hrootCard, card_blockedSignatureUpperSubsetLayer,
    card_blockedSignatureSubsetLayer] at hbound
  simpa [S] using hbound

/-- Combine the old factor-two lower union with the exact fiber-adaptive
sum.  Whichever is stronger survives together with the opposite tail face. -/
theorem max_twoWeight_rootAddSelectedFiberMass_add_negativeTailFace_le_fullCube
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    let S := canonicalSupportEscapeBlockedSignatures hh r
    max (2 * reducedCollisionWeight (m := m) r)
        (reducedCollisionWeight (m := m) r +
          selectedFiberSliceMass S r.val.2 r.val.2) +
      2 ^ (m - r.val.2.card) ≤ 2 ^ m := by
  classical
  dsimp only
  let S := canonicalSupportEscapeBlockedSignatures hh r
  have hfactor := two_mul_weight_add_tailFace_le_fullCube
    hg hh hh0 r hr hrmin hcover
  have hfiber :=
    weight_add_selectedFiberSliceMass_add_negativeTailFace_le_fullCube
      hg hh hh0 r hr hrmin hcover
  by_cases hle : 2 * reducedCollisionWeight (m := m) r ≤
      reducedCollisionWeight (m := m) r +
        selectedFiberSliceMass S r.val.2 r.val.2
  · rw [max_eq_right hle]
    simpa [S] using hfiber
  · rw [max_eq_left (Nat.le_of_not_ge hle)]
    exact hfactor

/-- In the genuine critical residual, the maximum of factor-two growth and
the exact selected-fiber mass is retained as a concrete one-root constraint. -/
theorem genuineDominant_max_factorTwo_fiberAdaptive_tailFace_bound
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    let hh := half_add_half
      (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
        rw [pow_succ]
        ring)
    let S := canonicalSupportEscapeBlockedSignatures hh r
    max (2 * reducedCollisionWeight (m := n) r)
        (reducedCollisionWeight (m := n) r +
          selectedFiberSliceMass S r.val.2 r.val.2) +
      2 ^ (n - r.val.2.card) ≤ 2 ^ n := by
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
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card := by
    simpa [hh, criticalCanonicalReducedCollisions,
      reducedCollisionSupport] using hdominant.2.1
  have hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2 := by
    simpa [hh] using hdominant.2.2.2.2.2.2.2.2.2.1
  simpa [hh] using
    max_twoWeight_rootAddSelectedFiberMass_add_negativeTailFace_le_fullCube
      hg hh (half_ne_zero hN hM) r hr' hrmin hcover

end CollisionFiberAdaptiveSlices

end MinModulus
