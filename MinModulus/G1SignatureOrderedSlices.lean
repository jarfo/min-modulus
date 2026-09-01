/-
# Ordered first-present signature slices

The exact-singleton slices fixed every negative-tail coordinate, while the
third-slice argument fixed only the two private half-cube coordinates and one
new covered coordinate.  Order all remaining covered coordinates.  At index
`i`, require its coordinate to be present and only the two private coordinates
and earlier ordered coordinates to be absent.  Later coordinates remain free.

The resulting slices are pairwise disjoint by their first present ordered
coordinate.  Their uniform floors form the geometric sum

`sum i : Fin t, 2^(padding-(i+3))`.
-/
import MinModulus.G1SignatureThirdSlice

namespace MinModulus

open Finset

variable {m : ℕ}

/-- The `i`-th coordinate of a finset in its inherited linear order. -/
noncomputable def orderedTailCoordinate
    (Q : Finset (Fin m)) (i : Fin Q.card) : Fin m :=
  Q.orderEmbOfFin rfl i

/-- The first `i+1` coordinates of `Q`, transported to the ambient type. -/
noncomputable def orderedTailPrefix
    (Q : Finset (Fin m)) (i : Fin Q.card) : Finset (Fin m) := by
  classical
  exact (Finset.Iic i).image (Q.orderEmbOfFin rfl)

/-- The two private coordinates together with the ordered prefix ending at
`i`. -/
noncomputable def orderedTailMarkerSet
    (Q : Finset (Fin m)) (j k : Fin m) (i : Fin Q.card) :
    Finset (Fin m) := by
  classical
  exact insert j (insert k (orderedTailPrefix Q i))

/-- The geometric surplus supplied by `t` ordered first-present slices. -/
def orderedGeometricTailSurplus (padding t : ℕ) : ℕ :=
  ∑ i : Fin t, 2 ^ (padding - (i.1 + 3))

theorem orderedTailCoordinate_mem
    (Q : Finset (Fin m)) (i : Fin Q.card) :
    orderedTailCoordinate Q i ∈ Q := by
  exact Q.orderEmbOfFin_mem rfl i

theorem orderedTailPrefix_subset
    (Q : Finset (Fin m)) (i : Fin Q.card) :
    orderedTailPrefix Q i ⊆ Q := by
  classical
  intro l hl
  rcases Finset.mem_image.mp hl with ⟨u, hu, rfl⟩
  exact orderedTailCoordinate_mem Q u

theorem orderedTailCoordinate_mem_prefix
    (Q : Finset (Fin m)) (i : Fin Q.card) :
    orderedTailCoordinate Q i ∈ orderedTailPrefix Q i := by
  classical
  exact Finset.mem_image.mpr ⟨i, by simp, rfl⟩

theorem orderedTailCoordinate_mem_laterPrefix
    (Q : Finset (Fin m)) {i u : Fin Q.card} (hiu : i < u) :
    orderedTailCoordinate Q i ∈ orderedTailPrefix Q u := by
  classical
  exact Finset.mem_image.mpr ⟨i, by simp [hiu.le], rfl⟩

theorem card_orderedTailPrefix
    (Q : Finset (Fin m)) (i : Fin Q.card) :
    (orderedTailPrefix Q i).card = i.1 + 1 := by
  classical
  rw [orderedTailPrefix, Finset.card_image_iff.mpr]
  · exact Fin.card_Iic i
  · intro u _ v _ huv
    exact (Q.orderEmbOfFin rfl).injective huv

theorem card_orderedTailMarkerSet
    (Q : Finset (Fin m)) (j k : Fin m) (i : Fin Q.card)
    (hjk : j ≠ k) (hjQ : j ∉ Q) (hkQ : k ∉ Q) :
    (orderedTailMarkerSet Q j k i).card = i.1 + 3 := by
  classical
  have hjPrefix : j ∉ orderedTailPrefix Q i :=
    fun hj ↦ hjQ (orderedTailPrefix_subset Q i hj)
  have hkPrefix : k ∉ orderedTailPrefix Q i :=
    fun hk ↦ hkQ (orderedTailPrefix_subset Q i hk)
  rw [orderedTailMarkerSet,
    Finset.card_insert_of_notMem (by simp [hjk, hjPrefix]),
    Finset.card_insert_of_notMem hkPrefix,
    card_orderedTailPrefix]

theorem orderedTailMarkerSet_subset
    (B Q : Finset (Fin m)) (j k : Fin m) (i : Fin Q.card)
    (hQB : Q ⊆ B) (hjB : j ∈ B) (hkB : k ∈ B) :
    orderedTailMarkerSet Q j k i ⊆ B := by
  classical
  intro l hl
  rcases Finset.mem_insert.mp hl with rfl | hl
  · exact hjB
  rcases Finset.mem_insert.mp hl with rfl | hl
  · exact hkB
  exact hQB (orderedTailPrefix_subset Q i hl)

theorem orderedTailCoordinate_mem_markerSet
    (Q : Finset (Fin m)) (j k : Fin m) (i : Fin Q.card) :
    orderedTailCoordinate Q i ∈ orderedTailMarkerSet Q j k i := by
  classical
  exact Finset.mem_insert_of_mem
    (Finset.mem_insert_of_mem (orderedTailCoordinate_mem_prefix Q i))

/-- A cover of `B` restricts to a cover of every sub-finset `T`. -/
theorem biUnion_sdiff_eq_self_of_subset_of_biUnion_sdiff_eq
    (S : Finset (Finset (Fin m))) (B T : Finset (Fin m))
    (hTB : T ⊆ B)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    S.biUnion (fun C ↦ T \ C) = T := by
  classical
  apply Finset.Subset.antisymm
  · intro l hl
    rcases Finset.mem_biUnion.mp hl with ⟨C, hC, hlTC⟩
    exact (Finset.mem_sdiff.mp hlTC).1
  · intro l hlT
    have hlCover : l ∈ S.biUnion (fun C ↦ B \ C) := by
      rw [hcover]
      exact hTB hlT
    rcases Finset.mem_biUnion.mp hlCover with ⟨C, hC, hlBC⟩
    exact Finset.mem_biUnion.mpr
      ⟨C, hC, Finset.mem_sdiff.mpr
        ⟨hlT, (Finset.mem_sdiff.mp hlBC).2⟩⟩

/-- Union of all realizing signature slices at one ordered marker. -/
noncomputable def coveredOrderedTailSliceAt
    (S : Finset (Finset (Fin m))) (Q : Finset (Fin m))
    (j k : Fin m) (i : Fin Q.card) : Finset (Finset (Fin m)) :=
  coveredSingletonTailSliceAt S (orderedTailMarkerSet Q j k i)
    (orderedTailCoordinate Q i)

/-- The complete ordered first-present slice family. -/
noncomputable def coveredOrderedTailSlices
    (S : Finset (Finset (Fin m))) (Q : Finset (Fin m))
    (j k : Fin m) : Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.biUnion (coveredOrderedTailSliceAt S Q j k)

/-- Each ordered slice union has its geometric cardinality floor. -/
theorem pow_padding_sub_orderedIndex_le_card_coveredOrderedAt
    (R B Q : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (j k : Fin m) (i : Fin Q.card)
    (hQB : Q ⊆ B) (hjB : j ∈ B) (hkB : k ∈ B)
    (hjk : j ≠ k) (hjQ : j ∉ Q) (hkQ : k ∉ Q)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    2 ^ (m - R.card - (i.1 + 3)) ≤
      (coveredOrderedTailSliceAt S Q j k i).card := by
  classical
  let T := orderedTailMarkerSet Q j k i
  let l := orderedTailCoordinate Q i
  have hTB : T ⊆ B :=
    orderedTailMarkerSet_subset B Q j k i hQB hjB hkB
  have hcoverT : S.biUnion (fun C ↦ T \ C) = T :=
    biUnion_sdiff_eq_self_of_subset_of_biUnion_sdiff_eq S B T hTB hcover
  have hlT : l ∈ T := orderedTailCoordinate_mem_markerSet Q j k i
  have hfloor := pow_padding_sub_tailCard_le_card_coveredAt
    R T S hcards hcoverT hlT
  simpa [T, l, coveredOrderedTailSliceAt,
    card_orderedTailMarkerSet Q j k i hjk hjQ hkQ] using hfloor

/-- Distinct ordered first-present slices are disjoint. -/
theorem coveredOrderedTailSliceAt_disjoint
    (S : Finset (Finset (Fin m))) (Q : Finset (Fin m))
    (j k : Fin m) {i u : Fin Q.card} (hiu : i ≠ u) :
    Disjoint (coveredOrderedTailSliceAt S Q j k i)
      (coveredOrderedTailSliceAt S Q j k u) := by
  classical
  rw [Finset.disjoint_left]
  intro U hUi hUu
  have hiInter := inter_tail_eq_singleton_of_mem_coveredAt
    S (orderedTailMarkerSet Q j k i) (orderedTailCoordinate Q i) hUi
  have huInter := inter_tail_eq_singleton_of_mem_coveredAt
    S (orderedTailMarkerSet Q j k u) (orderedTailCoordinate Q u) hUu
  rcases lt_or_gt_of_ne hiu with hiu' | hui'
  · have hiU : orderedTailCoordinate Q i ∈ U := by
      have hi : orderedTailCoordinate Q i ∈
          U ∩ orderedTailMarkerSet Q j k i := by
        rw [hiInter]
        simp
      exact (Finset.mem_inter.mp hi).1
    have hiMarker : orderedTailCoordinate Q i ∈
        orderedTailMarkerSet Q j k u := by
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (orderedTailCoordinate_mem_laterPrefix Q hiu'))
    have hiSingleton : orderedTailCoordinate Q i ∈
        ({orderedTailCoordinate Q u} : Finset (Fin m)) := by
      rw [← huInter]
      exact Finset.mem_inter.mpr ⟨hiU, hiMarker⟩
    have hcoord : orderedTailCoordinate Q i = orderedTailCoordinate Q u := by
      simpa using hiSingleton
    exact hiu ((Q.orderEmbOfFin rfl).injective hcoord)
  · have huU : orderedTailCoordinate Q u ∈ U := by
      have hu : orderedTailCoordinate Q u ∈
          U ∩ orderedTailMarkerSet Q j k u := by
        rw [huInter]
        simp
      exact (Finset.mem_inter.mp hu).1
    have huMarker : orderedTailCoordinate Q u ∈
        orderedTailMarkerSet Q j k i := by
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (orderedTailCoordinate_mem_laterPrefix Q hui'))
    have huSingleton : orderedTailCoordinate Q u ∈
        ({orderedTailCoordinate Q i} : Finset (Fin m)) := by
      rw [← hiInter]
      exact Finset.mem_inter.mpr ⟨huU, huMarker⟩
    have hcoord : orderedTailCoordinate Q u = orderedTailCoordinate Q i := by
      simpa using huSingleton
    exact hiu ((Q.orderEmbOfFin rfl).injective hcoord).symm

/-- Summing the pairwise disjoint ordered slices gives the full geometric
surplus. -/
theorem orderedGeometricTailSurplus_le_card_coveredOrderedSlices
    (R B Q : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (j k : Fin m)
    (hQB : Q ⊆ B) (hjB : j ∈ B) (hkB : k ∈ B)
    (hjk : j ≠ k) (hjQ : j ∉ Q) (hkQ : k ∉ Q)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    orderedGeometricTailSurplus (m - R.card) Q.card ≤
      (coveredOrderedTailSlices S Q j k).card := by
  classical
  have hpairwise :
      ((Finset.univ : Finset (Fin Q.card)) : Set (Fin Q.card)).PairwiseDisjoint
        (coveredOrderedTailSliceAt S Q j k) := by
    intro i hi u hu hiu
    exact coveredOrderedTailSliceAt_disjoint S Q j k hiu
  rw [coveredOrderedTailSlices, Finset.card_biUnion hpairwise]
  exact Finset.sum_le_sum fun i hi ↦
    pow_padding_sub_orderedIndex_le_card_coveredOrderedAt
      R B Q S j k i hQB hjB hkB hjk hjQ hkQ hcards hcover

/-- The complete covered-signature union contains the root, the two private
half-cubes, and every ordered first-present slice.  Thus the surplus beyond
`2w` is the full geometric sum indexed by the remaining tail coordinates. -/
theorem two_mul_root_add_orderedGeometricTailSurplus_le_covered_signature_union
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        orderedGeometricTailSurplus (m - R.card) (B.card - 2) ≤
      (rootAndBlockedSignatureSubsetUnion R S).card := by
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
  let O := coveredOrderedTailSlices S Q j k
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
  have hkQmem : k ∈ B.erase j := by simp [hkB, hjk.symm]
  have hQcard : Q.card + 2 = B.card := by
    have hkCard := Finset.card_erase_add_one hkQmem
    have hjCard := Finset.card_erase_add_one hjB
    change ((B.erase j).erase k).card + 2 = B.card
    omega
  have hQcard' : Q.card = B.card - 2 := by omega
  have hQB : Q ⊆ B := by
    intro l hl
    have hl' : l ∈ (B.erase j).erase k := by simpa [Q] using hl
    exact (Finset.mem_erase.mp (Finset.mem_erase.mp hl').2).2
  have hjQ : j ∉ Q := by simp [Q]
  have hkQ : k ∉ Q := by simp [Q]
  have hOcard :
      orderedGeometricTailSurplus (m - R.card) (B.card - 2) ≤ O.card := by
    have hbound :=
      orderedGeometricTailSurplus_le_card_coveredOrderedSlices
        R B Q S j k hQB hjB hkB hjk hjQ hkQ hcards hcover
    simpa [O, hQcard'] using hbound
  have hKO : Disjoint K O := by
    rw [Finset.disjoint_left]
    intro U hUK hUO
    have hUO' : U ∈ coveredOrderedTailSlices S Q j k := by
      simpa [O] using hUO
    have hi : ∃ i, U ∈ coveredOrderedTailSliceAt S Q j k i := by
      simpa [coveredOrderedTailSlices] using hUO'
    rcases hi with ⟨i, hUi⟩
    let l := orderedTailCoordinate Q i
    let T := orderedTailMarkerSet Q j k i
    have hlQ : l ∈ Q := orderedTailCoordinate_mem Q i
    have hlB : l ∈ B := hQB hlQ
    have hlj : l ≠ j := by
      intro hlj
      apply hjQ
      rw [← hlj]
      exact hlQ
    have hlk : l ≠ k := by
      intro hlk
      apply hkQ
      rw [← hlk]
      exact hlQ
    have hInter : U ∩ T = {l} := by
      exact inter_tail_eq_singleton_of_mem_coveredAt
        S T l (by simpa [coveredOrderedTailSliceAt, T, l] using hUi)
    have hlInter : l ∈ U ∩ T := by rw [hInter]; simp
    have hlU := (Finset.mem_inter.mp hlInter).1
    have hjT : j ∈ T := by simp [T, orderedTailMarkerSet]
    have hkT : k ∈ T := by simp [T, orderedTailMarkerSet]
    rcases Finset.mem_union.mp hUK with hURC | hUHD
    · rcases Finset.mem_union.mp hURC with hUR | hUHC
      · have hallowed := Finset.mem_powerset.mp hUR
        have hlAllowed := hallowed hlU
        exact (Finset.mem_sdiff.mp hlAllowed).2 (hBR hlB)
      · have hjU : j ∈ U := (Finset.mem_filter.mp hUHC).2
        have hjInter : j ∈ U ∩ T :=
          Finset.mem_inter.mpr ⟨hjU, hjT⟩
        have hjSingleton : j ∈ ({l} : Finset (Fin m)) := by
          rw [← hInter]
          exact hjInter
        have hjEq : j = l := by simpa using hjSingleton
        exact hlj hjEq.symm
    · have hkU : k ∈ U := (Finset.mem_filter.mp hUHD).2
      have hkInter : k ∈ U ∩ T :=
        Finset.mem_inter.mpr ⟨hkU, hkT⟩
      have hkSingleton : k ∈ ({l} : Finset (Fin m)) := by
        rw [← hInter]
        exact hkInter
      have hkEq : k = l := by simpa using hkSingleton
      exact hlk hkEq.symm
  have hsmallCard :
      2 * (blockedSignatureSubsetLayer R).card +
          orderedGeometricTailSurplus (m - R.card) (B.card - 2) ≤
        (K ∪ O).card := by
    rw [Finset.card_union_of_disjoint hKO, hKcard]
    exact Nat.add_le_add_left hOcard _
  have hsmallSubset : K ∪ O ⊆
      rootAndBlockedSignatureSubsetUnion R S := by
    intro U hU
    rcases Finset.mem_union.mp hU with hUK | hUO
    · rcases Finset.mem_union.mp hUK with hURC | hUHD
      · rcases Finset.mem_union.mp hURC with hUR | hUHC
        · exact Finset.mem_union_left _ hUR
        · exact Finset.mem_union_right _
            (Finset.mem_biUnion.mpr ⟨C, hC,
              blockedSignatureContainingSubsetLayer_subset C j hUHC⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨D, hD,
            blockedSignatureContainingSubsetLayer_subset D k hUHD⟩)
    · have hUO' : U ∈ coveredOrderedTailSlices S Q j k := by
        simpa [O] using hUO
      have hi : ∃ i, U ∈ coveredOrderedTailSliceAt S Q j k i := by
        simpa [coveredOrderedTailSlices] using hUO'
      rcases hi with ⟨i, hUi⟩
      rcases Finset.mem_biUnion.mp (by
          simpa [coveredOrderedTailSliceAt,
            coveredSingletonTailSliceAt] using hUi) with
        ⟨E, hE, hUE⟩
      split at hUE
      next hlE =>
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨E, hE,
            blockedSignatureSingletonTailSlice_subset E
              (orderedTailMarkerSet Q j k i)
              (orderedTailCoordinate Q i)
              (Finset.mem_sdiff.mpr hlE) hUE⟩)
      next hlE => simp at hUE
  exact hsmallCard.trans (Finset.card_mono hsmallSubset)

/-- Adjoining the disjoint opposite tail face preserves the complete ordered
geometric surplus. -/
theorem two_mul_root_add_orderedGeometricTailSurplus_add_tailFace_le_unionWithUpper
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        orderedGeometricTailSurplus (m - R.card) (B.card - 2) +
          (blockedSignatureSubsetLayer B).card ≤
      (rootAndBlockedSignatureSubsetUnionWithUpper B R S).card := by
  classical
  have hlower :=
    two_mul_root_add_orderedGeometricTailSurplus_le_covered_signature_union
      R B S hB hBR hcards hcover hinter
  have hBRinter : (B ∩ R).Nonempty := by
    obtain ⟨j, hjB⟩ := hB
    exact ⟨j, Finset.mem_inter.mpr ⟨hjB, hBR hjB⟩⟩
  rw [card_rootAndBlockedSignatureSubsetUnionWithUpper
    B R S hBRinter hinter]
  omega

/-- Full Boolean-cube consequence of all ordered first-present slices. -/
theorem two_mul_root_add_orderedGeometricTailSurplus_add_tailFace_le_fullCube
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card +
        orderedGeometricTailSurplus (m - R.card) (B.card - 2) +
          (blockedSignatureSubsetLayer B).card ≤ 2 ^ m := by
  classical
  have henriched :=
    two_mul_root_add_orderedGeometricTailSurplus_add_tailFace_le_unionWithUpper
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
  exact henriched.trans hcube

section CollisionOrderedSlices

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Actual collision-family form of the ordered geometric full-cube bound. -/
theorem two_mul_weight_add_orderedGeometricTailSurplus_add_negativeTailFace_le_fullCube
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
        orderedGeometricTailSurplus
          (m - (reducedCollisionSupport r).card) (r.val.2.card - 2) +
          2 ^ (m - r.val.2.card) ≤ 2 ^ m := by
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
    two_mul_root_add_orderedGeometricTailSurplus_add_tailFace_le_fullCube
      R r.val.2 S hB hBR hcards hcover' hinter
  have hrootCard : (blockedSignatureSubsetLayer R).card =
      reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  simpa [hrootCard, card_blockedSignatureSubsetLayer] using hbound

/-- Hybrid subset-cube estimate retaining the whole ordered geometric
surplus with no right-hand error. -/
theorem rootWeight_add_orderedGeometricTailSurplus_add_tailUpperCards_le_fullCube_add_contamination
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
        orderedGeometricTailSurplus
          (m - (reducedCollisionSupport r).card) (r.val.2.card - 2) +
        (blockedSignatureUpperSubsetLayer r.val.1).card +
          (blockedSignatureUpperSubsetLayer r.val.2).card ≤
      2 ^ m + (positiveUpperSignatureContamination hh r).card := by
  classical
  let R := reducedCollisionSupport r
  let S := canonicalSupportEscapeBlockedSignatures hh r
  let E := rootAndBlockedSignatureSubsetUnionWithUpper r.val.2 R S
  let UA := blockedSignatureUpperSubsetLayer r.val.1
  let F := E ∪ UA
  let u := orderedGeometricTailSurplus (m - R.card) (r.val.2.card - 2)
  have hBR : r.val.2 ⊆ R := by
    intro j hj
    exact Finset.mem_union_right _ hj
  have hcards : ∀ C ∈ S, C.card = R.card := by
    intro C hC
    exact card_escapeBlockedSignature_eq_rootSupport hh r hrmin hC
  have hcover' : S.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 := by
    change canonicalSupportEscapeBlockedSignatureCoverage hh r = r.val.2
    exact hcover
  have hE : 2 * (blockedSignatureSubsetLayer R).card + u +
      (blockedSignatureSubsetLayer r.val.2).card ≤ E.card := by
    exact
      two_mul_root_add_orderedGeometricTailSurplus_add_tailFace_le_unionWithUpper
        R r.val.2 S hB hBR hcards hcover' hBinter
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
      2 * (blockedSignatureSubsetLayer R).card + u +
          (blockedSignatureUpperSubsetLayer r.val.2).card + UA.card ≤
        E.card + UA.card := by
    exact Nat.add_le_add_right hE UA.card
  have htotal := hmass.trans hcombined
  change (blockedSignatureSubsetLayer R).card + u + UA.card +
      (blockedSignatureUpperSubsetLayer r.val.2).card ≤
    2 ^ m + (positiveUpperSignatureContamination hh r).card
  omega

/-- Scaled hybrid crossing inequality retaining the full ordered geometric
surplus. -/
theorem pow_positiveCard_mul_rootWeight_add_orderedGeometricTailSurplus_add_tailUpperCards_le_fullCube_add_crossMass
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
    let u := orderedGeometricTailSurplus
      (m - (reducedCollisionSupport r).card) (r.val.2.card - 2)
    2 ^ r.val.1.card *
        (reducedCollisionWeight (m := m) r + u +
          2 ^ (m - r.val.1.card) + 2 ^ (m - r.val.2.card)) ≤
      2 ^ r.val.1.card * 2 ^ m +
        (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
          reducedCollisionWeight (m := m) p.1 *
            reducedCollisionWeight (m := m) p.2) := by
  dsimp only
  have hB := canonicalReducedCollision_negative_tail_nonempty
    g hg hh hh0 hr
  have hBinter : ∀ C ∈ canonicalSupportEscapeBlockedSignatures hh r,
      (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hcube :=
    rootWeight_add_orderedGeometricTailSurplus_add_tailUpperCards_le_fullCube_add_contamination
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
        (2 ^ m + (positiveUpperSignatureContamination hh r).card) := hscaled
    _ = 2 ^ r.val.1.card * 2 ^ m +
        2 ^ r.val.1.card *
          (positiveUpperSignatureContamination hh r).card := by ring
    _ ≤ _ := Nat.add_le_add_left hcharge _

/-- Critical small-crossing sandwich retaining all ordered first-present
slices.  The statement applies uniformly, including the zero-surplus
two-coordinate tail profile. -/
theorem criticalSmallCrossDominant_orderedGeometricTailSurplus_hybrid_sandwich
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hA : r.val.1.Nonempty) :
    let u := orderedGeometricTailSurplus
      (n - (reducedCollisionSupport r).card) (r.val.2.card - 2)
    4 * (2 ^ r.val.1.card *
        (reducedCollisionWeight (m := n) r + u +
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
  have hrmin : ∀ v ∈ canonicalReducedCollisions (g := g)
      (half_add_half hN),
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport v).card := by
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
    pow_positiveCard_mul_rootWeight_add_orderedGeometricTailSurplus_add_tailUpperCards_le_fullCube_add_crossMass
      hg (half_add_half hN) (half_ne_zero hN hM) r hr' hrmin hcover hA
  have hhybrid' :
      2 ^ r.val.1.card *
          (reducedCollisionWeight (m := n) r +
            orderedGeometricTailSurplus
              (n - (reducedCollisionSupport r).card) (r.val.2.card - 2) +
            2 ^ (n - r.val.1.card) + 2 ^ (n - r.val.2.card)) ≤
        2 ^ r.val.1.card * 2 ^ n + criticalCanonicalCrossMass g := by
    simpa [criticalCanonicalCrossMass,
      criticalCanonicalPositiveNegativeCrossPairs] using hhybrid
  have hsmall := hres.1.2
  omega

end CollisionOrderedSlices

end MinModulus
