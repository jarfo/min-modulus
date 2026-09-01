/-
# Padding-weighted singleton tail slices

The linear surplus from `G1SignatureTailSurplus` counted one singleton for
each tail coordinate beyond the two private half-cube coordinates.  A
realizing signature contains a much larger canonical slice: all allowed
subsets whose intersection with the source tail is exactly that singleton.

For a blocked signature `C` covering `j ∈ B`, this slice has size
`2^(m-|C∪B|)`.  When `|C|=|R|`, it is uniformly at least
`2^(m-|R|-|B|)`.  Slices indexed by distinct tail coordinates are disjoint.
-/
import MinModulus.G1SignatureTailSurplus

namespace MinModulus

open Finset

variable {m : ℕ}

/-- The part of a blocked-signature layer whose intersection with `B` is
exactly the singleton `{j}`.  It is parametrized by freely adjoining subsets
outside both `C` and `B`. -/
noncomputable def blockedSignatureSingletonTailSlice
    (C B : Finset (Fin m)) (j : Fin m) : Finset (Finset (Fin m)) := by
  classical
  exact ((Finset.univ \ (C ∪ B)).powerset).image (fun U ↦ insert j U)

/-- Exact intrinsic characterization of a singleton-tail slice. -/
theorem mem_blockedSignatureSingletonTailSlice_iff
    (C B : Finset (Fin m)) (j : Fin m) (hj : j ∈ B \ C)
    (U : Finset (Fin m)) :
    U ∈ blockedSignatureSingletonTailSlice C B j ↔
      U ⊆ Finset.univ \ C ∧ U ∩ B = {j} := by
  classical
  constructor
  · intro hU
    rcases Finset.mem_image.mp hU with ⟨V, hV, rfl⟩
    have hVsub := Finset.mem_powerset.mp hV
    have hjB := (Finset.mem_sdiff.mp hj).1
    have hjC := (Finset.mem_sdiff.mp hj).2
    constructor
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxV
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjC⟩
      · have hxFree := Finset.mem_sdiff.mp (hVsub hxV)
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, fun hxC ↦ hxFree.2 (Finset.mem_union_left _ hxC)⟩
    · ext x
      constructor
      · intro hx
        have hxInsert := (Finset.mem_inter.mp hx).1
        have hxB := (Finset.mem_inter.mp hx).2
        rcases Finset.mem_insert.mp hxInsert with rfl | hxV
        · simp
        · have hxFree := Finset.mem_sdiff.mp (hVsub hxV)
          exact False.elim (hxFree.2 (Finset.mem_union_right _ hxB))
      · intro hx
        have hxj : x = j := by simpa using hx
        subst x
        exact Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _, hjB⟩
  · rintro ⟨hUsub, hUB⟩
    have hjU : j ∈ U := by
      have : j ∈ U ∩ B := by rw [hUB]; simp
      exact (Finset.mem_inter.mp this).1
    apply Finset.mem_image.mpr
    refine ⟨U.erase j, ?_, insert_erase hjU⟩
    apply Finset.mem_powerset.mpr
    intro x hx
    have hxU := Finset.mem_of_mem_erase hx
    have hxj := Finset.ne_of_mem_erase hx
    have hxAllowed := Finset.mem_sdiff.mp (hUsub hxU)
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hxCB
    rcases Finset.mem_union.mp hxCB with hxC | hxB
    · exact hxAllowed.2 hxC
    · have hxInter : x ∈ U ∩ B :=
        Finset.mem_inter.mpr ⟨hxU, hxB⟩
      have hxSingleton : x ∈ ({j} : Finset (Fin m)) := by
        rw [← hUB]
        exact hxInter
      exact hxj (by simpa using hxSingleton)

/-- Exact cardinality of a singleton-tail slice. -/
theorem card_blockedSignatureSingletonTailSlice
    (C B : Finset (Fin m)) (j : Fin m) (hjB : j ∈ B) :
    (blockedSignatureSingletonTailSlice C B j).card =
      2 ^ (m - (C ∪ B).card) := by
  classical
  rw [blockedSignatureSingletonTailSlice,
    Finset.card_image_iff.mpr]
  · rw [Finset.card_powerset,
      Finset.card_sdiff_of_subset (Finset.subset_univ (C ∪ B)),
      Finset.card_univ, Fintype.card_fin]
  · intro U hU V hV hUV
    have hUsub := Finset.mem_powerset.mp hU
    have hVsub := Finset.mem_powerset.mp hV
    have hjU : j ∉ U := by
      intro hjU
      have hjFree := Finset.mem_sdiff.mp (hUsub hjU)
      exact hjFree.2 (Finset.mem_union_right _ hjB)
    have hjV : j ∉ V := by
      intro hjV
      have hjFree := Finset.mem_sdiff.mp (hVsub hjV)
      exact hjFree.2 (Finset.mem_union_right _ hjB)
    change insert j U = insert j V at hUV
    calc
      U = (insert j U).erase j := (Finset.erase_insert hjU).symm
      _ = (insert j V).erase j := by rw [hUV]
      _ = V := Finset.erase_insert hjV

/-- Equal root/signature cardinality gives a uniform slice floor depending
only on root padding and the full tail size. -/
theorem pow_padding_sub_tailCard_le_singletonTailSlice
    (R C B : Finset (Fin m)) (j : Fin m)
    (hCR : C.card = R.card) (hjB : j ∈ B) :
    2 ^ (m - R.card - B.card) ≤
      (blockedSignatureSingletonTailSlice C B j).card := by
  rw [card_blockedSignatureSingletonTailSlice C B j hjB]
  apply Nat.pow_le_pow_right (by norm_num)
  have hunion : (C ∪ B).card ≤ C.card + B.card := Finset.card_union_le _ _
  omega

/-- A singleton-tail slice lies in its complete blocked-signature layer. -/
theorem blockedSignatureSingletonTailSlice_subset
    (C B : Finset (Fin m)) (j : Fin m) (hj : j ∈ B \ C) :
    blockedSignatureSingletonTailSlice C B j ⊆
      blockedSignatureSubsetLayer C := by
  intro U hU
  apply Finset.mem_powerset.mpr
  exact ((mem_blockedSignatureSingletonTailSlice_iff C B j hj U).mp hU).1

/-- Every set in the slice has the prescribed singleton intersection. -/
theorem inter_tail_eq_singleton_of_mem_singletonTailSlice
    (C B : Finset (Fin m)) (j : Fin m) (hj : j ∈ B \ C)
    {U : Finset (Fin m)}
    (hU : U ∈ blockedSignatureSingletonTailSlice C B j) :
    U ∩ B = {j} :=
  ((mem_blockedSignatureSingletonTailSlice_iff C B j hj U).mp hU).2

/-- Slices with distinct prescribed tail coordinates are disjoint. -/
theorem blockedSignatureSingletonTailSlices_disjoint
    (C D B : Finset (Fin m)) (j k : Fin m)
    (hj : j ∈ B \ C) (hk : k ∈ B \ D) (hjk : j ≠ k) :
    Disjoint (blockedSignatureSingletonTailSlice C B j)
      (blockedSignatureSingletonTailSlice D B k) := by
  rw [Finset.disjoint_left]
  intro U hUj hUk
  have hjInter := inter_tail_eq_singleton_of_mem_singletonTailSlice
    C B j hj hUj
  have hkInter := inter_tail_eq_singleton_of_mem_singletonTailSlice
    D B k hk hUk
  have : ({j} : Finset (Fin m)) = {k} := by rw [← hjInter, hkInter]
  exact hjk (by simpa using this)

/-- Union of all realizing signature slices for one covered coordinate. -/
noncomputable def coveredSingletonTailSliceAt
    (S : Finset (Finset (Fin m))) (B : Finset (Fin m)) (j : Fin m) :
    Finset (Finset (Fin m)) := by
  classical
  exact S.biUnion (fun C ↦
    if hj : j ∈ B \ C then blockedSignatureSingletonTailSlice C B j else ∅)

/-- A realizing signature slice is contained in the full slice union at its
covered coordinate. -/
theorem singletonTailSlice_subset_coveredAt
    (S : Finset (Finset (Fin m))) (B C : Finset (Fin m)) (j : Fin m)
    (hC : C ∈ S) (hj : j ∈ B \ C) :
    blockedSignatureSingletonTailSlice C B j ⊆
      coveredSingletonTailSliceAt S B j := by
  classical
  intro U hU
  apply Finset.mem_biUnion.mpr
  exact ⟨C, hC, by simpa [hj] using hU⟩

/-- Every member of a coordinate-indexed union has that singleton tail
intersection. -/
theorem inter_tail_eq_singleton_of_mem_coveredAt
    (S : Finset (Finset (Fin m))) (B : Finset (Fin m)) (j : Fin m)
    {U : Finset (Fin m)} (hU : U ∈ coveredSingletonTailSliceAt S B j) :
    U ∩ B = {j} := by
  classical
  rcases Finset.mem_biUnion.mp hU with ⟨C, hC, hUC⟩
  split at hUC
  next hj =>
    exact inter_tail_eq_singleton_of_mem_singletonTailSlice C B j hj hUC
  next hj => simp at hUC

/-- Coordinate-indexed unions remain pairwise disjoint. -/
theorem coveredSingletonTailSliceAt_disjoint
    (S : Finset (Finset (Fin m))) (B : Finset (Fin m))
    {j k : Fin m} (hjk : j ≠ k) :
    Disjoint (coveredSingletonTailSliceAt S B j)
      (coveredSingletonTailSliceAt S B k) := by
  rw [Finset.disjoint_left]
  intro U hUj hUk
  have hjInter := inter_tail_eq_singleton_of_mem_coveredAt S B j hUj
  have hkInter := inter_tail_eq_singleton_of_mem_coveredAt S B k hUk
  have : ({j} : Finset (Fin m)) = {k} := by rw [← hjInter, hkInter]
  exact hjk (by simpa using this)

/-- All singleton-tail slice unions indexed by a chosen coordinate set. -/
noncomputable def coveredSingletonTailSlices
    (S : Finset (Finset (Fin m))) (B Q : Finset (Fin m)) :
    Finset (Finset (Fin m)) := by
  classical
  exact Q.biUnion (coveredSingletonTailSliceAt S B)

/-- A covered coordinate contributes at least the uniform padding-tail floor
to its slice union. -/
theorem pow_padding_sub_tailCard_le_card_coveredAt
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    {j : Fin m} (hjB : j ∈ B) :
    2 ^ (m - R.card - B.card) ≤
      (coveredSingletonTailSliceAt S B j).card := by
  classical
  have hjCover : j ∈ S.biUnion (fun C ↦ B \ C) := by
    rw [hcover]
    exact hjB
  rcases Finset.mem_biUnion.mp hjCover with ⟨C, hC, hjC⟩
  exact (pow_padding_sub_tailCard_le_singletonTailSlice
      R C B j (hcards C hC) hjB).trans
    (Finset.card_le_card
      (singletonTailSlice_subset_coveredAt S B C j hC hjC))

/-- Pairwise disjoint coordinate slices sum to a padding-weighted tail
surplus. -/
theorem card_mul_pow_padding_sub_tailCard_le_coveredSlices
    (R B Q : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hQB : Q ⊆ B)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    Q.card * 2 ^ (m - R.card - B.card) ≤
      (coveredSingletonTailSlices S B Q).card := by
  classical
  have hpairwise : (Q : Set (Fin m)).PairwiseDisjoint
      (coveredSingletonTailSliceAt S B) := by
    intro j hjQ k hkQ hjk
    exact coveredSingletonTailSliceAt_disjoint S B hjk
  rw [coveredSingletonTailSlices, Finset.card_biUnion hpairwise]
  calc
    Q.card * 2 ^ (m - R.card - B.card) =
        Q.sum (fun _ ↦ 2 ^ (m - R.card - B.card)) := by simp
    _ ≤ Q.sum (fun j ↦ (coveredSingletonTailSliceAt S B j).card) :=
      Finset.sum_le_sum fun j hjQ ↦
        pow_padding_sub_tailCard_le_card_coveredAt
          R B S hcards hcover (hQB hjQ)

/-- Padding-weighted refinement of the covered-signature lower union.  Each
tail coordinate beyond the two private half-cube coordinates contributes a
whole disjoint slice of size at least `2^(padding-|B|)`. -/
theorem two_mul_root_add_tailCard_mul_sliceWeight_le_covered_union_add_two_sliceWeights
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        B.card * 2 ^ (m - R.card - B.card) ≤
      (rootAndBlockedSignatureSubsetUnion R S).card +
        2 * 2 ^ (m - R.card - B.card) := by
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
  let SQ := coveredSingletonTailSlices S B Q
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
  have hQB : Q ⊆ B := by
    intro l hl
    have hl' : l ∈ (B.erase j).erase k := by simpa [Q] using hl
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hl').2).2
  have hSQcard : Q.card * 2 ^ (m - R.card - B.card) ≤ SQ.card := by
    exact card_mul_pow_padding_sub_tailCard_le_coveredSlices
      R B Q S hQB hcards hcover
  have hKSQ : Disjoint K SQ := by
    rw [Finset.disjoint_left]
    intro U hUK hUSQ
    rcases Finset.mem_biUnion.mp hUSQ with ⟨l, hlQ, hUl⟩
    have hlQ' : l ∈ (B.erase j).erase k := by simpa [Q] using hlQ
    have hlB : l ∈ B :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hlQ').2).2
    have hlj : l ≠ j :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hlQ').2).1
    have hlk : l ≠ k := (Finset.mem_erase.mp hlQ').1
    have hInter := inter_tail_eq_singleton_of_mem_coveredAt S B l hUl
    have hlInter : l ∈ U ∩ B := by rw [hInter]; simp
    have hlU := (Finset.mem_inter.mp hlInter).1
    rcases Finset.mem_union.mp hUK with hURC | hUHD
    · rcases Finset.mem_union.mp hURC with hUR | hUHC
      · have hallowed := Finset.mem_powerset.mp hUR
        have hlAllowed := hallowed hlU
        exact (Finset.mem_sdiff.mp hlAllowed).2 (hBR hlB)
      · have hjU : j ∈ U := (Finset.mem_filter.mp hUHC).2
        have hjInter : j ∈ U ∩ B :=
          Finset.mem_inter.mpr ⟨hjU, hjB⟩
        have hjSingleton : j ∈ ({l} : Finset (Fin m)) := by
          rw [← hInter]
          exact hjInter
        have hjEq : j = l := by simpa using hjSingleton
        exact hlj hjEq.symm
    · have hkU : k ∈ U := (Finset.mem_filter.mp hUHD).2
      have hkInter : k ∈ U ∩ B :=
        Finset.mem_inter.mpr ⟨hkU, hkB⟩
      have hkSingleton : k ∈ ({l} : Finset (Fin m)) := by
        rw [← hInter]
        exact hkInter
      have hkEq : k = l := by simpa using hkSingleton
      exact hlk hkEq.symm
  have hsmallCard :
      2 * (blockedSignatureSubsetLayer R).card +
          Q.card * 2 ^ (m - R.card - B.card) ≤ (K ∪ SQ).card := by
    rw [Finset.card_union_of_disjoint hKSQ, hKcard]
    exact Nat.add_le_add_left hSQcard _
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
    · rcases Finset.mem_biUnion.mp hUSQ with ⟨l, hlQ, hUl⟩
      rcases Finset.mem_biUnion.mp hUl with ⟨E, hE, hUE⟩
      split at hUE
      next hlE =>
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨E, hE,
            blockedSignatureSingletonTailSlice_subset E B l hlE hUE⟩)
      next hlE => simp at hUE
  have hsmallToUnion := hsmallCard.trans (Finset.card_mono hsmallSubset)
  calc
    2 * (blockedSignatureSubsetLayer R).card +
        B.card * 2 ^ (m - R.card - B.card) =
      (2 * (blockedSignatureSubsetLayer R).card +
        Q.card * 2 ^ (m - R.card - B.card)) +
          2 * 2 ^ (m - R.card - B.card) := by
        rw [← hQcard]
        ring
    _ ≤ (rootAndBlockedSignatureSubsetUnion R S).card +
        2 * 2 ^ (m - R.card - B.card) :=
      Nat.add_le_add_right hsmallToUnion _

/-- Adjoining the disjoint opposite tail face preserves the full
padding-weighted slice surplus. -/
theorem two_mul_root_add_weightedTail_add_tailFace_le_unionWithUpper_add_error
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        B.card * 2 ^ (m - R.card - B.card) +
          (blockedSignatureSubsetLayer B).card ≤
      (rootAndBlockedSignatureSubsetUnionWithUpper B R S).card +
        2 * 2 ^ (m - R.card - B.card) := by
  classical
  have hlower :=
    two_mul_root_add_tailCard_mul_sliceWeight_le_covered_union_add_two_sliceWeights
      R B S hB hBR hcards hcover hinter
  have hBRinter : (B ∩ R).Nonempty := by
    obtain ⟨j, hjB⟩ := hB
    exact ⟨j, Finset.mem_inter.mpr ⟨hjB, hBR hjB⟩⟩
  rw [card_rootAndBlockedSignatureSubsetUnionWithUpper
    B R S hBRinter hinter]
  omega

/-- Full Boolean-cube consequence of the padding-weighted tail slices. -/
theorem two_mul_root_add_weightedTail_add_tailFace_le_fullCube_add_error
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        B.card * 2 ^ (m - R.card - B.card) +
          (blockedSignatureSubsetLayer B).card ≤
      2 ^ m + 2 * 2 ^ (m - R.card - B.card) := by
  classical
  have henriched :=
    two_mul_root_add_weightedTail_add_tailFace_le_unionWithUpper_add_error
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
  exact henriched.trans
    (Nat.add_le_add_right hcube (2 * 2 ^ (m - R.card - B.card)))

section CollisionTailSlices

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Actual collision-family form of the padding-weighted tail-face bound. -/
theorem two_mul_weight_add_weightedNegativeTail_add_tailFace_le_fullCube_add_error
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    2 * reducedCollisionWeight (m := m) r +
        r.val.2.card *
          2 ^ (m - (reducedCollisionSupport r).card - r.val.2.card) +
        2 ^ (m - r.val.2.card) ≤
      2 ^ m +
        2 * 2 ^ (m - (reducedCollisionSupport r).card - r.val.2.card) := by
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
    two_mul_root_add_weightedTail_add_tailFace_le_fullCube_add_error
      R r.val.2 S hB hBR hcards hcover' hinter
  have hrootCard : (blockedSignatureSubsetLayer R).card =
      reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  simpa [hrootCard, card_blockedSignatureSubsetLayer] using hbound

/-- Hybrid subset-cube estimate retaining the padding-weighted tail surplus. -/
theorem rootWeight_add_weightedNegativeTail_add_tailUpperCards_le_fullCube_add_contamination_add_error
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
        r.val.2.card *
          2 ^ (m - (reducedCollisionSupport r).card - r.val.2.card) +
        (blockedSignatureUpperSubsetLayer r.val.1).card +
          (blockedSignatureUpperSubsetLayer r.val.2).card ≤
      2 ^ m + (positiveUpperSignatureContamination hh r).card +
        2 * 2 ^
          (m - (reducedCollisionSupport r).card - r.val.2.card) := by
  classical
  let R := reducedCollisionSupport r
  let S := canonicalSupportEscapeBlockedSignatures hh r
  let E := rootAndBlockedSignatureSubsetUnionWithUpper r.val.2 R S
  let UA := blockedSignatureUpperSubsetLayer r.val.1
  let F := E ∪ UA
  let t := 2 ^ (m - R.card - r.val.2.card)
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
      r.val.2.card * t + (blockedSignatureSubsetLayer r.val.2).card ≤
        E.card + 2 * t := by
    exact two_mul_root_add_weightedTail_add_tailFace_le_unionWithUpper_add_error
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
      2 * (blockedSignatureSubsetLayer R).card + r.val.2.card * t +
          (blockedSignatureUpperSubsetLayer r.val.2).card + UA.card ≤
        E.card + UA.card + 2 * t := by
    omega
  have htotal := hmass.trans
    (Nat.add_le_add_right hcombined (2 * t))
  change (blockedSignatureSubsetLayer R).card + r.val.2.card * t + UA.card +
      (blockedSignatureUpperSubsetLayer r.val.2).card ≤
    2 ^ m + (positiveUpperSignatureContamination hh r).card + 2 * t
  omega

/-- Final padding-weighted hybrid crossing inequality. -/
theorem pow_positiveCard_mul_rootWeight_add_weightedNegativeTail_add_tailUpperCards_le_fullCube_add_crossMass_add_error
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
    let t := 2 ^
      (m - (reducedCollisionSupport r).card - r.val.2.card)
    2 ^ r.val.1.card *
        (reducedCollisionWeight (m := m) r + r.val.2.card * t +
          2 ^ (m - r.val.1.card) + 2 ^ (m - r.val.2.card)) ≤
      2 ^ r.val.1.card * 2 ^ m +
        (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) +
        2 ^ r.val.1.card * (2 * t) := by
  dsimp only
  have hB := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  have hBinter : ∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hcube :=
    rootWeight_add_weightedNegativeTail_add_tailUpperCards_le_fullCube_add_contamination_add_error
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
    _ ≤ 2 ^ r.val.1.card *
        (2 ^ m + (positiveUpperSignatureContamination hh r).card +
          2 * 2 ^ (m - (reducedCollisionSupport r).card - r.val.2.card)) :=
      hscaled
    _ = 2 ^ r.val.1.card * 2 ^ m +
        2 ^ r.val.1.card *
          (positiveUpperSignatureContamination hh r).card +
        2 ^ r.val.1.card *
          (2 * 2 ^ (m - (reducedCollisionSupport r).card - r.val.2.card)) := by
      ring
    _ ≤ _ :=
      Nat.add_le_add_right
        (Nat.add_le_add_left hcharge (2 ^ r.val.1.card * 2 ^ m)) _

/-- Critical small-crossing sandwich retaining the full padding-weighted tail
slice surplus. -/
theorem criticalSmallCrossDominant_tailSlice_hybrid_sandwich
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hA : r.val.1.Nonempty) :
    let t := 2 ^
      (n - (reducedCollisionSupport r).card - r.val.2.card)
    4 * (2 ^ r.val.1.card *
        (reducedCollisionWeight (m := n) r + r.val.2.card * t +
          2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card))) <
      4 * (2 ^ r.val.1.card * 2 ^ n) +
        criticalHalfGap n s * criticalHalfGap n s +
        4 * (2 ^ r.val.1.card * (2 * t)) := by
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
    pow_positiveCard_mul_rootWeight_add_weightedNegativeTail_add_tailUpperCards_le_fullCube_add_crossMass_add_error
      hg (half_add_half hN) (half_ne_zero hN hM) r hr' hrmin hcover hA
  have hhybrid' :
      2 ^ r.val.1.card *
          (reducedCollisionWeight (m := n) r + r.val.2.card *
              2 ^ (n - (reducedCollisionSupport r).card - r.val.2.card) +
            2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card)) ≤
        2 ^ r.val.1.card * 2 ^ n + criticalCanonicalCrossMass g +
          2 ^ r.val.1.card *
            (2 * 2 ^
              (n - (reducedCollisionSupport r).card - r.val.2.card)) := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs] using hhybrid
  have hsmall := hres.1.2
  omega

end CollisionTailSlices

end MinModulus
