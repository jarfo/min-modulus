/-
# Sharper coordinate-subcube growth from signature-fiber coverage

The second-moment estimate uses only pairwise overlap and therefore ignores
the exact coordinate coverage `⋃ C, (B_r \ C) = B_r`.  This file begins the
sharper Boolean-cube count which uses that extra information.

The key finite-cover dichotomy is elementary but decisive.  Either one
signature drops every coordinate of `B_r`, or two realized dropped sets are
incomparable.  In the first branch, the exact root/signature intersection is
smaller by a factor `2^|B_r|`.  In the second branch, each of the two
signatures has a coordinate allowed there but blocked by the root and by the
other signature; the corresponding containing-coordinate half-layers are
disjoint and, together with the root, have total size `2 w_r`.
-/
import MinModulus.G1LayerSecondMoment

namespace MinModulus

open Finset

variable {α : Type*} [DecidableEq α]

/-- The half of the coordinate subcube `𝒫(A)` whose members contain `j`. -/
def powersetContaining (A : Finset α) (j : α) : Finset (Finset α) :=
  A.powerset.filter (fun U ↦ j ∈ U)

/-- Fixing one available Boolean coordinate to one leaves exactly half of a
coordinate subcube. -/
theorem card_powersetContaining (A : Finset α) (j : α) (hj : j ∈ A) :
    (powersetContaining A j).card = 2 ^ (A.card - 1) := by
  classical
  have hcard : (A.erase j).powerset.card = (powersetContaining A j).card := by
    apply Finset.card_bij (fun U _ ↦ insert j U)
    · intro U hU
      rw [mem_powerset] at hU
      simp only [powersetContaining, mem_filter, mem_powerset, mem_insert,
        true_or, and_true]
      exact (insert_subset_iff.mpr ⟨hj, hU.trans (erase_subset j A)⟩)
    · intro U hU V hV huv
      rw [mem_powerset] at hU hV
      have hjU : j ∉ U := not_mem_subset hU (by simp)
      have hjV : j ∉ V := not_mem_subset hV (by simp)
      calc
        U = (insert j U).erase j := (erase_insert hjU).symm
        _ = (insert j V).erase j := by rw [huv]
        _ = V := erase_insert hjV
    · intro V hV
      rw [powersetContaining, mem_filter, mem_powerset] at hV
      refine ⟨V.erase j, ?_, insert_erase hV.2⟩
      rw [mem_powerset]
      exact erase_subset_erase j hV.1
  simpa [card_powerset, card_erase_of_mem hj] using hcard.symm

/-- A finite cover by relative complements either has one member covering
everything or contains two incomparable members. -/
theorem finset_sdiff_cover_single_or_incomparable
    (S : Finset (Finset α)) (B : Finset α) (hB : B.Nonempty)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    (∃ C ∈ S, B ⊆ B \ C) ∨
      ∃ C ∈ S, ∃ D ∈ S,
        ((B \ C) \ (B \ D)).Nonempty ∧
          ((B \ D) \ (B \ C)).Nonempty := by
  classical
  by_cases hsingle : ∃ C ∈ S, B ⊆ B \ C
  · exact Or.inl hsingle
  · right
    have hS : S.Nonempty := by
      obtain ⟨j, hjB⟩ := hB
      have hjcover : j ∈ S.biUnion (fun C ↦ B \ C) := by
        rw [hcover]
        exact hjB
      rcases Finset.mem_biUnion.mp hjcover with ⟨C, hC, hjC⟩
      exact ⟨C, hC⟩
    obtain ⟨C, hC, hCmax⟩ :=
      Finset.exists_max_image S (fun D ↦ (B \ D).card) hS
    have hnotFull : ¬B ⊆ B \ C := by
      intro hfull
      exact hsingle ⟨C, hC, hfull⟩
    have hnotSubsetUnion : ¬B ⊆ B \ C := hnotFull
    obtain ⟨j, hjB, hjC⟩ : ∃ j, j ∈ B ∧ j ∉ B \ C := by
      simpa [Finset.not_subset] using hnotSubsetUnion
    have hjcover : j ∈ S.biUnion (fun D ↦ B \ D) := by
      rw [hcover]
      exact hjB
    rcases Finset.mem_biUnion.mp hjcover with ⟨D, hD, hjD⟩
    refine ⟨C, hC, D, hD, ?_, ?_⟩
    · by_contra hdiff
      have hsubset : B \ C ⊆ B \ D := by
        exact not_not.mp (Finset.sdiff_nonempty.not.mp hdiff)
      have hcardle := hCmax D hD
      have heq : B \ C = B \ D :=
        Finset.eq_of_subset_of_card_le hsubset hcardle
      exact hjC (by simpa [heq] using hjD)
    · exact Finset.sdiff_nonempty.mpr fun hsubset ↦ hjC (hsubset hjD)

section SignatureSubcubes

variable {m : ℕ}

/-- The half of a blocked-signature layer in which an allowed coordinate is
present. -/
noncomputable def blockedSignatureContainingSubsetLayer
    (C : Finset (Fin m)) (j : Fin m) : Finset (Finset (Fin m)) :=
  powersetContaining (Finset.univ \ C) j

/-- Exact size of an intrinsic blocked-signature subset layer. -/
theorem card_blockedSignatureSubsetLayer (C : Finset (Fin m)) :
    (blockedSignatureSubsetLayer C).card = 2 ^ (m - C.card) := by
  classical
  rw [blockedSignatureSubsetLayer, Finset.card_powerset,
    Finset.card_sdiff_of_subset (Finset.subset_univ C)]
  simp

/-- An allowed coordinate cuts a blocked-signature subset layer exactly in
half. -/
theorem card_blockedSignatureContainingSubsetLayer
    (C : Finset (Fin m)) (j : Fin m) (hj : j ∉ C) :
    (blockedSignatureContainingSubsetLayer C j).card =
      2 ^ (m - C.card - 1) := by
  classical
  rw [blockedSignatureContainingSubsetLayer,
    card_powersetContaining (Finset.univ \ C) j (by simp [hj]),
    Finset.card_sdiff_of_subset (Finset.subset_univ C)]
  simp

/-- The containing-coordinate half-layer is contained in its full signature
layer. -/
theorem blockedSignatureContainingSubsetLayer_subset
    (C : Finset (Fin m)) (j : Fin m) :
    blockedSignatureContainingSubsetLayer C j ⊆
      blockedSignatureSubsetLayer C := by
  classical
  intro U hU
  exact (Finset.mem_filter.mp hU).1

/-- A half-layer forcing `j` is disjoint from every signature layer which
blocks `j`. -/
theorem blockedSignatureContainingSubsetLayer_disjoint
    (C D : Finset (Fin m)) (j : Fin m) (hjD : j ∈ D) :
    Disjoint (blockedSignatureContainingSubsetLayer C j)
      (blockedSignatureSubsetLayer D) := by
  classical
  rw [Finset.disjoint_left]
  intro U hUC hUD
  have hjU : j ∈ U := (Finset.mem_filter.mp hUC).2
  have hUallowed := Finset.mem_powerset.mp hUD
  exact (Finset.mem_sdiff.mp (hUallowed hjU)).2 hjD

/-- Two incomparable dropped-coordinate fibers yield two private half-cubes.
Together with the root cube they give a full factor-two subset-layer union. -/
theorem two_mul_card_blockedSignatureSubsetLayer_le_three_union_of_incomparable
    (R C D B : Finset (Fin m))
    (hBR : B ⊆ R)
    (hCR : C.card = R.card) (hDR : D.card = R.card)
    (hinc : ((B \ C) \ (B \ D)).Nonempty ∧
      ((B \ D) \ (B \ C)).Nonempty) :
    2 * (blockedSignatureSubsetLayer R).card ≤
      (blockedSignatureSubsetLayer R ∪
        blockedSignatureSubsetLayer C ∪
          blockedSignatureSubsetLayer D).card := by
  classical
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
  have hjR : j ∈ R := hBR hjB
  have hkR : k ∈ R := hBR hkB
  let HC := blockedSignatureContainingSubsetLayer C j
  let HD := blockedSignatureContainingSubsetLayer D k
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
  have hsmallCard :
      ((blockedSignatureSubsetLayer R ∪ HC) ∪ HD).card =
        (blockedSignatureSubsetLayer R).card + HC.card + HD.card := by
    rw [Finset.card_union_of_disjoint hRootC_D,
      Finset.card_union_of_disjoint hRootC, Nat.add_assoc]
  have hp : 0 < m - R.card := by
    have hjAllowed : j ∈ Finset.univ \ C := by simp [hjC]
    have hpos : 0 < (Finset.univ \ C).card :=
      Finset.card_pos.mpr ⟨j, hjAllowed⟩
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ C)] at hpos
    simpa [hCR] using hpos
  have hhalfC : 2 * HC.card = (blockedSignatureSubsetLayer R).card := by
    rw [card_blockedSignatureSubsetLayer,
      show HC.card = 2 ^ (m - C.card - 1) by
        exact card_blockedSignatureContainingSubsetLayer C j hjC,
      hCR]
    simpa [Nat.mul_comm] using Nat.two_pow_pred_mul_two hp
  have hhalfD : 2 * HD.card = (blockedSignatureSubsetLayer R).card := by
    rw [card_blockedSignatureSubsetLayer,
      show HD.card = 2 ^ (m - D.card - 1) by
        exact card_blockedSignatureContainingSubsetLayer D k hkD,
      hDR]
    simpa [Nat.mul_comm] using Nat.two_pow_pred_mul_two hp
  have hsmallSubset :
      (blockedSignatureSubsetLayer R ∪ HC) ∪ HD ⊆
        blockedSignatureSubsetLayer R ∪
          blockedSignatureSubsetLayer C ∪
            blockedSignatureSubsetLayer D := by
    intro U hU
    rcases Finset.mem_union.mp hU with hURC | hUHD
    · rcases Finset.mem_union.mp hURC with hUR | hUHC
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ hUR)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (blockedSignatureContainingSubsetLayer_subset C j hUHC))
    · exact Finset.mem_union_right _
        (blockedSignatureContainingSubsetLayer_subset D k hUHD)
  calc
    2 * (blockedSignatureSubsetLayer R).card =
        ((blockedSignatureSubsetLayer R ∪ HC) ∪ HD).card := by omega
    _ ≤ (blockedSignatureSubsetLayer R ∪
        blockedSignatureSubsetLayer C ∪
          blockedSignatureSubsetLayer D).card := Finset.card_mono hsmallSubset

/-- Exact subset-level intersection of two blocked-signature subcubes. -/
theorem blockedSignatureSubsetLayers_inter
    (R C : Finset (Fin m)) :
    blockedSignatureSubsetLayer R ∩ blockedSignatureSubsetLayer C =
      ((Finset.univ \ R) ∩ (Finset.univ \ C)).powerset := by
  classical
  ext U
  simp only [blockedSignatureSubsetLayer, Finset.mem_inter,
    Finset.mem_powerset]
  exact Finset.subset_inter_iff.symm

/-- If one equal-cardinality signature drops all of `B ⊆ R`, its union with
the root misses from a factor-two union by at most a `2^-|B|` fraction.  The
subtraction-free scaled form is convenient over natural cardinalities. -/
theorem pow_card_mul_two_mul_root_le_single_union_add_root
    (R C B : Finset (Fin m))
    (hBR : B ⊆ R) (hCR : C.card = R.card)
    (hdrop : B ⊆ B \ C) :
    2 ^ B.card * (2 * (blockedSignatureSubsetLayer R).card) ≤
      2 ^ B.card *
          (blockedSignatureSubsetLayer R ∪
            blockedSignatureSubsetLayer C).card +
        (blockedSignatureSubsetLayer R).card := by
  classical
  let AR := Finset.univ \ R
  let I := (Finset.univ \ R) ∩ (Finset.univ \ C)
  let E := C \ R
  have hBRC : B ⊆ R \ C := by
    intro j hjB
    exact Finset.mem_sdiff.mpr
      ⟨hBR hjB, (Finset.mem_sdiff.mp (hdrop hjB)).2⟩
  have hdiffCard : (R \ C).card = (C \ R).card := by
    simp only [Finset.card_sdiff]
    rw [hCR, Finset.inter_comm C R]
  have hBE : B.card ≤ E.card := by
    calc
      B.card ≤ (R \ C).card := Finset.card_le_card hBRC
      _ = E.card := hdiffCard
  have hIE : Disjoint I E := by
    rw [Finset.disjoint_left]
    intro j hjI hjE
    have hjnotC : j ∉ C :=
      (Finset.mem_sdiff.mp (Finset.mem_inter.mp hjI).2).2
    exact hjnotC (Finset.mem_sdiff.mp hjE).1
  have hIE_AR : I ∪ E ⊆ AR := by
    intro j hj
    rcases Finset.mem_union.mp hj with hjI | hjE
    · exact (Finset.mem_inter.mp hjI).1
    · exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hjE).2⟩
  have hdim : I.card + B.card ≤ AR.card := by
    calc
      I.card + B.card ≤ I.card + E.card := Nat.add_le_add_left hBE I.card
      _ = (I ∪ E).card := (Finset.card_union_of_disjoint hIE).symm
      _ ≤ AR.card := Finset.card_mono hIE_AR
  have hinterCard :
      (blockedSignatureSubsetLayer R ∩
          blockedSignatureSubsetLayer C).card = 2 ^ I.card := by
    rw [blockedSignatureSubsetLayers_inter, Finset.card_powerset]
  have hrootCard :
      (blockedSignatureSubsetLayer R).card = 2 ^ AR.card := by
    rw [card_blockedSignatureSubsetLayer]
    simp only [AR, Finset.card_sdiff_of_subset (Finset.subset_univ R),
      Finset.card_univ, Fintype.card_fin]
  have hpow :
      2 ^ B.card *
          (blockedSignatureSubsetLayer R ∩
            blockedSignatureSubsetLayer C).card ≤
        (blockedSignatureSubsetLayer R).card := by
    rw [hinterCard, hrootCard, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by simpa [Nat.add_comm] using hdim)
  have hlayerCards :
      (blockedSignatureSubsetLayer C).card =
        (blockedSignatureSubsetLayer R).card := by
    rw [card_blockedSignatureSubsetLayer,
      card_blockedSignatureSubsetLayer, hCR]
  have hunionInter :
      (blockedSignatureSubsetLayer R ∪
          blockedSignatureSubsetLayer C).card +
        (blockedSignatureSubsetLayer R ∩
          blockedSignatureSubsetLayer C).card =
        2 * (blockedSignatureSubsetLayer R).card := by
    rw [Finset.card_union_add_card_inter, hlayerCards]
    omega
  calc
    2 ^ B.card * (2 * (blockedSignatureSubsetLayer R).card) =
        2 ^ B.card *
          ((blockedSignatureSubsetLayer R ∪
              blockedSignatureSubsetLayer C).card +
            (blockedSignatureSubsetLayer R ∩
              blockedSignatureSubsetLayer C).card) := by rw [hunionInter]
    _ = 2 ^ B.card *
          (blockedSignatureSubsetLayer R ∪
            blockedSignatureSubsetLayer C).card +
        2 ^ B.card *
          (blockedSignatureSubsetLayer R ∩
            blockedSignatureSubsetLayer C).card := Nat.mul_add _ _ _
    _ ≤ 2 ^ B.card *
          (blockedSignatureSubsetLayer R ∪
            blockedSignatureSubsetLayer C).card +
        (blockedSignatureSubsetLayer R).card :=
      Nat.add_le_add_left hpow _

/-- Union of a finite family of intrinsic blocked-signature subset layers. -/
noncomputable def blockedSignatureSubsetUnion
    (S : Finset (Finset (Fin m))) : Finset (Finset (Fin m)) :=
  S.biUnion blockedSignatureSubsetLayer

/-- Root subset layer together with every layer in a signature family. -/
noncomputable def rootAndBlockedSignatureSubsetUnion
    (R : Finset (Fin m)) (S : Finset (Finset (Fin m))) :
    Finset (Finset (Fin m)) :=
  blockedSignatureSubsetLayer R ∪ blockedSignatureSubsetUnion S

/-- Sharp coordinate-coverage estimate for an equal-codimension family of
Boolean subcubes.  If their dropped fibers cover a nonempty `B ⊆ R`, the
root-plus-family union has size at least `(2 - 2^-|B|)` root layers. -/
theorem pow_card_mul_two_mul_root_le_covered_signature_union_add_root
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    2 ^ B.card * (2 * (blockedSignatureSubsetLayer R).card) ≤
      2 ^ B.card * (rootAndBlockedSignatureSubsetUnion R S).card +
        (blockedSignatureSubsetLayer R).card := by
  classical
  rcases finset_sdiff_cover_single_or_incomparable S B hB hcover with
    hsingle | hincomparable
  · rcases hsingle with ⟨C, hC, hdrop⟩
    have hpair := pow_card_mul_two_mul_root_le_single_union_add_root
      R C B hBR (hcards C hC) hdrop
    have hpairSubset :
        blockedSignatureSubsetLayer R ∪ blockedSignatureSubsetLayer C ⊆
          rootAndBlockedSignatureSubsetUnion R S := by
      intro U hU
      rcases Finset.mem_union.mp hU with hUR | hUC
      · exact Finset.mem_union_left _ hUR
      · exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨C, hC, hUC⟩)
    calc
      2 ^ B.card * (2 * (blockedSignatureSubsetLayer R).card) ≤
          2 ^ B.card *
              (blockedSignatureSubsetLayer R ∪
                blockedSignatureSubsetLayer C).card +
            (blockedSignatureSubsetLayer R).card := hpair
      _ ≤ 2 ^ B.card * (rootAndBlockedSignatureSubsetUnion R S).card +
            (blockedSignatureSubsetLayer R).card :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_left _ (Finset.card_mono hpairSubset)) _
  · rcases hincomparable with ⟨C, hC, D, hD, hinc⟩
    have hthree :=
      two_mul_card_blockedSignatureSubsetLayer_le_three_union_of_incomparable
        R C D B hBR (hcards C hC) (hcards D hD) hinc
    have hthreeSubset :
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
    have htwo :
        2 * (blockedSignatureSubsetLayer R).card ≤
          (rootAndBlockedSignatureSubsetUnion R S).card :=
      hthree.trans (Finset.card_mono hthreeSubset)
    calc
      2 ^ B.card * (2 * (blockedSignatureSubsetLayer R).card) ≤
          2 ^ B.card * (rootAndBlockedSignatureSubsetUnion R S).card :=
        Nat.mul_le_mul_left _ htwo
      _ ≤ 2 ^ B.card * (rootAndBlockedSignatureSubsetUnion R S).card +
          (blockedSignatureSubsetLayer R).card := Nat.le_add_right _ _

end SignatureSubcubes

section CriticalSignatureApplication

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Mapping a union of signature subset layers is the union of the mapped
value layers. -/
theorem image_blockedSignatureSubsetUnion
    (g : Fin (m + 1) → G) (S : Finset (Finset (Fin m))) :
    (blockedSignatureSubsetUnion S).image (ssum g) =
      S.biUnion (blockedSignatureValueLayer g) := by
  classical
  ext x
  constructor
  · intro hx
    rcases Finset.mem_image.mp hx with ⟨U, hU, rfl⟩
    rcases Finset.mem_biUnion.mp hU with ⟨C, hC, hUC⟩
    exact Finset.mem_biUnion.mpr
      ⟨C, hC, Finset.mem_image.mpr ⟨U, hUC, rfl⟩⟩
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨C, hC, hxC⟩
    rcases Finset.mem_image.mp hxC with ⟨U, hUC, rfl⟩
    exact Finset.mem_image.mpr
      ⟨U, Finset.mem_biUnion.mpr ⟨C, hC, hUC⟩, rfl⟩

omit [DecidableEq G] in
/-- The ordinary root padding cube is the intrinsic signature subcube whose
blocked set is the root collision support. -/
theorem collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) :
    collisionPaddingSubsetLayer r =
      blockedSignatureSubsetLayer (reducedCollisionSupport r) := by
  classical
  ext U
  rw [mem_collisionPaddingSubsetLayer_iff]
  simp only [blockedSignatureSubsetLayer, Finset.mem_powerset]

/-- The subset-level root-plus-family union maps exactly to the value-level
union used in the critical residual. -/
theorem image_rootAndEscapeBlockedSignatureSubsetUnion
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (rootAndBlockedSignatureSubsetUnion (reducedCollisionSupport r)
        (canonicalSupportEscapeBlockedSignatures hh r)).image (ssum g) =
      rootAndEscapeBlockedSignatureValueUnion hh r := by
  classical
  rw [rootAndBlockedSignatureSubsetUnion, Finset.image_union,
    image_blockedSignatureSubsetUnion]
  unfold rootAndEscapeBlockedSignatureValueUnion
  unfold canonicalSupportEscapeBlockedSignatureValueUnion
  rw [collisionPaddingValueLayer,
    collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r]

/-- Coordinate coverage upgrades the pairwise second-moment estimate to the
sharp `(2 - 2^-|B_r|)` union lower bound for the actual subset-sum value
layers in the dominant escape branch. -/
theorem pow_sourceTailCard_mul_two_mul_weight_le_signatureValueUnion_add_weight
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hB : r.val.2.Nonempty)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    2 ^ r.val.2.card *
        (2 * reducedCollisionWeight (m := m) r) ≤
      2 ^ r.val.2.card *
          (rootAndEscapeBlockedSignatureValueUnion hh r).card +
        reducedCollisionWeight (m := m) r := by
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
  have hsubset :=
    pow_card_mul_two_mul_root_le_covered_signature_union_add_root
      R r.val.2 S hB hBR hcards hcover'
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

end CriticalSignatureApplication

end MinModulus
