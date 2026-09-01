/-
# A disjoint negative-tail upper face for the covered signature union

The sharp coordinate-cover estimate still counts only lower Boolean faces:
the root layer and the restored signature layers all have the form
`𝒫(univ \ C)`.  There is a much larger face available for free: the upper
face consisting of subsets containing every coordinate of the root negative
tail `B_r`.  It is disjoint from the root lower face, and it is disjoint from
a signature lower face whenever that signature meets `B_r`.

Canonical negative tails are pairwise intersecting.  Since restoration never
removes a root coordinate, every realized blocked signature meets `B_r`
itself.  Thus the `B_r`-upper face, of size `2^(m-|B_r|)`, is disjoint from
the entire covered signature union.
-/
import MinModulus.G1SignatureSubcubeCoverage

namespace MinModulus

open Finset

section UpperFaceSubcubes

variable {m : ℕ}

/-- The Boolean face whose subsets contain the whole blocked set `R`. -/
noncomputable def blockedSignatureUpperSubsetLayer
    (R : Finset (Fin m)) : Finset (Finset (Fin m)) :=
  (Finset.univ \ R).powerset.image (fun U ↦ R ∪ U)

@[simp] theorem mem_blockedSignatureUpperSubsetLayer_iff
    {R U : Finset (Fin m)} :
    U ∈ blockedSignatureUpperSubsetLayer R ↔ R ⊆ U := by
  classical
  constructor
  · intro hU
    rcases Finset.mem_image.mp hU with ⟨V, _, rfl⟩
    exact Finset.subset_union_left
  · intro hRU
    apply Finset.mem_image.mpr
    refine ⟨U \ R, ?_, Finset.union_sdiff_of_subset hRU⟩
    rw [Finset.mem_powerset]
    intro j hj
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hj).2⟩

/-- The upper face has the same cardinality as the corresponding lower
face. -/
theorem card_blockedSignatureUpperSubsetLayer (R : Finset (Fin m)) :
    (blockedSignatureUpperSubsetLayer R).card =
      (blockedSignatureSubsetLayer R).card := by
  classical
  have hinj : Set.InjOn (fun U : Finset (Fin m) ↦ R ∪ U)
      ↑(Finset.univ \ R).powerset := by
    intro U hU V hV huv
    have hUsub := Finset.mem_powerset.mp hU
    have hVsub := Finset.mem_powerset.mp hV
    have hRU : Disjoint R U := by
      rw [Finset.disjoint_left]
      intro j hjR hjU
      exact (Finset.mem_sdiff.mp (hUsub hjU)).2 hjR
    have hRV : Disjoint R V := by
      rw [Finset.disjoint_left]
      intro j hjR hjV
      exact (Finset.mem_sdiff.mp (hVsub hjV)).2 hjR
    change R ∪ U = R ∪ V at huv
    calc
      U = (R ∪ U) \ R := (Finset.union_sdiff_cancel_left hRU).symm
      _ = (R ∪ V) \ R := by rw [huv]
      _ = V := Finset.union_sdiff_cancel_left hRV
  rw [blockedSignatureUpperSubsetLayer,
    (Finset.card_image_iff.mpr hinj),
    blockedSignatureSubsetLayer]

/-- The `B`-upper face has reciprocal dimension to the `2^|B|` scaling in
the sharp coverage theorem. -/
theorem pow_card_mul_card_blockedSignatureSubsetLayer
    (B : Finset (Fin m)) :
    2 ^ B.card * (blockedSignatureSubsetLayer B).card = 2 ^ m := by
  rw [card_blockedSignatureSubsetLayer, ← pow_add]
  congr 1
  exact Nat.add_sub_of_le (by simpa using Finset.card_le_univ B)

/-- If `R` and `C` meet, the face containing all of `R` is disjoint from the
face avoiding all of `C`. -/
theorem blockedSignatureUpperSubsetLayer_disjoint
    (R C : Finset (Fin m)) (hRC : (R ∩ C).Nonempty) :
    Disjoint (blockedSignatureUpperSubsetLayer R)
      (blockedSignatureSubsetLayer C) := by
  classical
  rw [Finset.disjoint_left]
  intro U hUpper hLower
  obtain ⟨j, hj⟩ := hRC
  have hjR := (Finset.mem_inter.mp hj).1
  have hjC := (Finset.mem_inter.mp hj).2
  have hjU := (mem_blockedSignatureUpperSubsetLayer_iff.mp hUpper) hjR
  have hUallowed := Finset.mem_powerset.mp hLower
  exact (Finset.mem_sdiff.mp (hUallowed hjU)).2 hjC

/-- If `T` meets the root and every signature, its upper face is disjoint
from the complete root-plus-signature lower union. -/
theorem blockedSignatureUpperSubsetLayer_disjoint_rootAndUnion
    (T R : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hTR : (T ∩ R).Nonempty)
    (hinter : ∀ C ∈ S, (T ∩ C).Nonempty) :
    Disjoint (blockedSignatureUpperSubsetLayer T)
      (rootAndBlockedSignatureSubsetUnion R S) := by
  classical
  rw [Finset.disjoint_left]
  intro U hUpper hLower
  rcases Finset.mem_union.mp hLower with hRoot | hFamily
  · exact (Finset.disjoint_left.mp
      (blockedSignatureUpperSubsetLayer_disjoint T R hTR))
        hUpper hRoot
  · rcases Finset.mem_biUnion.mp hFamily with ⟨C, hC, hUC⟩
    exact (Finset.disjoint_left.mp
      (blockedSignatureUpperSubsetLayer_disjoint T C (hinter C hC)))
        hUpper hUC

/-- The covered lower union together with an upper face hitting every blocked
signature. -/
noncomputable def rootAndBlockedSignatureSubsetUnionWithUpper
    (T R : Finset (Fin m)) (S : Finset (Finset (Fin m))) :
    Finset (Finset (Fin m)) :=
  rootAndBlockedSignatureSubsetUnion R S ∪
    blockedSignatureUpperSubsetLayer T

/-- Exact cardinality gained by adjoining a disjoint hitting upper face. -/
theorem card_rootAndBlockedSignatureSubsetUnionWithUpper
    (T R : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hTR : (T ∩ R).Nonempty)
    (hinter : ∀ C ∈ S, (T ∩ C).Nonempty) :
    (rootAndBlockedSignatureSubsetUnionWithUpper T R S).card =
      (rootAndBlockedSignatureSubsetUnion R S).card +
        (blockedSignatureSubsetLayer T).card := by
  classical
  rw [rootAndBlockedSignatureSubsetUnionWithUpper,
    Finset.card_union_of_disjoint
      (blockedSignatureUpperSubsetLayer_disjoint_rootAndUnion
        T R S hTR hinter).symm,
    card_blockedSignatureUpperSubsetLayer]

/-- Coordinate coverage plus the disjoint `B`-upper face gives the covered
lower-union bound together with a full `2^(m-|B|)` face. -/
theorem pow_card_mul_two_root_add_tailFace_le_covered_unionWithUpper_add_root
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 ^ B.card *
        (2 * (blockedSignatureSubsetLayer R).card +
          (blockedSignatureSubsetLayer B).card) ≤
      2 ^ B.card *
          (rootAndBlockedSignatureSubsetUnionWithUpper B R S).card +
        (blockedSignatureSubsetLayer R).card := by
  classical
  have hsharp :=
    pow_card_mul_two_mul_root_le_covered_signature_union_add_root
      R B S hB hBR hcards hcover
  have hBRinter : (B ∩ R).Nonempty := by
    obtain ⟨j, hjB⟩ := hB
    exact ⟨j, Finset.mem_inter.mpr ⟨hjB, hBR hjB⟩⟩
  rw [card_rootAndBlockedSignatureSubsetUnionWithUpper
    B R S hBRinter hinter]
  calc
    2 ^ B.card * (2 * (blockedSignatureSubsetLayer R).card +
        (blockedSignatureSubsetLayer B).card) =
        2 ^ B.card * (2 * (blockedSignatureSubsetLayer R).card) +
          2 ^ B.card * (blockedSignatureSubsetLayer B).card := by ring
    _ ≤ (2 ^ B.card * (rootAndBlockedSignatureSubsetUnion R S).card +
          (blockedSignatureSubsetLayer R).card) +
        2 ^ B.card * (blockedSignatureSubsetLayer B).card :=
      Nat.add_le_add_right hsharp _
    _ = 2 ^ B.card *
          ((rootAndBlockedSignatureSubsetUnion R S).card +
            (blockedSignatureSubsetLayer B).card) +
        (blockedSignatureSubsetLayer R).card := by ring

/-- Clean form of the enriched count: the scaled `B`-upper face contributes
exactly one whole anchored Boolean cube. -/
theorem pow_card_mul_two_root_add_fullCube_le_covered_unionWithUpper_add_root
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 ^ B.card * (2 * (blockedSignatureSubsetLayer R).card) + 2 ^ m ≤
      2 ^ B.card *
          (rootAndBlockedSignatureSubsetUnionWithUpper B R S).card +
        (blockedSignatureSubsetLayer R).card := by
  have h :=
    pow_card_mul_two_root_add_tailFace_le_covered_unionWithUpper_add_root
      R B S hB hBR hcards hcover hinter
  rw [← pow_card_mul_card_blockedSignatureSubsetLayer B]
  simpa [Nat.mul_add] using h

/-- Pure numerical consequence inside the full Boolean cube. -/
theorem pow_card_mul_two_root_add_tailFace_le_fullCube_add_root
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 ^ B.card *
        (2 * (blockedSignatureSubsetLayer R).card +
          (blockedSignatureSubsetLayer B).card) ≤
      2 ^ B.card * 2 ^ m + (blockedSignatureSubsetLayer R).card := by
  classical
  have hsharp :=
    pow_card_mul_two_root_add_tailFace_le_covered_unionWithUpper_add_root
      R B S hB hBR hcards hcover hinter
  have hsubset : rootAndBlockedSignatureSubsetUnionWithUpper B R S ⊆
      (Finset.univ : Finset (Fin m)).powerset := by
    intro U _
    exact Finset.mem_powerset.mpr (Finset.subset_univ U)
  calc
    2 ^ B.card * (2 * (blockedSignatureSubsetLayer R).card +
        (blockedSignatureSubsetLayer B).card) ≤
        2 ^ B.card *
            (rootAndBlockedSignatureSubsetUnionWithUpper B R S).card +
          (blockedSignatureSubsetLayer R).card := hsharp
    _ ≤ 2 ^ B.card * ((Finset.univ : Finset (Fin m)).powerset.card) +
          (blockedSignatureSubsetLayer R).card :=
      Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (Finset.card_mono hsubset)) _
    _ = 2 ^ B.card * 2 ^ m +
          (blockedSignatureSubsetLayer R).card := by
      rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]

/-- Clean full-cube numerical consequence of the negative-tail upper face. -/
theorem pow_card_mul_two_root_add_fullCube_le_scaled_fullCube_add_root
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hB : B.Nonempty) (hBR : B ⊆ R)
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (hinter : ∀ C ∈ S, (B ∩ C).Nonempty) :
    2 ^ B.card * (2 * (blockedSignatureSubsetLayer R).card) + 2 ^ m ≤
      2 ^ B.card * 2 ^ m + (blockedSignatureSubsetLayer R).card := by
  have h := pow_card_mul_two_root_add_tailFace_le_fullCube_add_root
    R B S hB hBR hcards hcover hinter
  calc
    2 ^ B.card * (2 * (blockedSignatureSubsetLayer R).card) + 2 ^ m =
        2 ^ B.card *
          (2 * (blockedSignatureSubsetLayer R).card +
            (blockedSignatureSubsetLayer B).card) := by
      rw [← pow_card_mul_card_blockedSignatureSubsetLayer B]
      ring
    _ ≤ 2 ^ B.card * 2 ^ m +
        (blockedSignatureSubsetLayer R).card := h

end UpperFaceSubcubes

section CriticalUpperFace

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Every realized blocked signature meets the root negative tail.  This is the
canonical negative-tail intersection, protected from restoration because
restoration uses only coordinates external to the root. -/
theorem sourceTail_inter_escapeBlockedSignature_nonempty
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    {C : Finset (Fin m)}
    (hC : C ∈ canonicalSupportEscapeBlockedSignatures hh r) :
    (r.val.2 ∩ C).Nonempty := by
  classical
  rcases mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC with
    ⟨q, hqtarget, hqC⟩
  rcases mem_canonicalSupportEscapeTargets_iff.mp hqtarget with ⟨j, hjq⟩
  have hq := (mem_canonicalSupportEscapeIncidences_iff.mp hjq).2.1
  have hinter := canonicalReducedCollision_negative_tails_inter
    g hg hh hh0 r q
      (mem_canonicalReducedCollisions_iff.mp hr)
      (mem_canonicalReducedCollisions_iff.mp hq)
  obtain ⟨k, hk⟩ := hinter
  have hkr := (Finset.mem_inter.mp hk).1
  have hkq := (Finset.mem_inter.mp hk).2
  refine ⟨k, Finset.mem_inter.mpr ⟨hkr, ?_⟩⟩
  rw [← hqC]
  exact (mem_restoredCollisionBlockedSupport_iff_of_mem_rootSupport
      r q (hrmin q hq) (Finset.mem_union_right _ hkr)).2
    (Finset.mem_union_right _ hkq)

/-- Group values of the opposite root face. -/
noncomputable def blockedSignatureUpperValueLayer
    (g : Fin (m + 1) → G) (R : Finset (Fin m)) : Finset G :=
  (blockedSignatureUpperSubsetLayer R).image (ssum g)

/-- The sharp covered value union enlarged by its disjoint opposite root
face. -/
noncomputable def rootAndEscapeBlockedSignatureValueUnionWithUpper
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Finset G :=
  rootAndEscapeBlockedSignatureValueUnion hh r ∪
    blockedSignatureUpperValueLayer g r.val.2

/-- The enriched subset union maps exactly to the enriched value union. -/
theorem image_rootAndEscapeBlockedSignatureSubsetUnionWithUpper
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (rootAndBlockedSignatureSubsetUnionWithUpper
        r.val.2 (reducedCollisionSupport r)
        (canonicalSupportEscapeBlockedSignatures hh r)).image (ssum g) =
      rootAndEscapeBlockedSignatureValueUnionWithUpper hh r := by
  classical
  rw [rootAndBlockedSignatureSubsetUnionWithUpper, Finset.image_union,
    image_rootAndEscapeBlockedSignatureSubsetUnion]
  rfl

/-- Actual dominant-escape values contain the sharp covered lower union and
the disjoint `B_r`-upper face. -/
theorem pow_sourceTailCard_mul_two_weight_add_tailFace_le_unionWithUpper_add_weight
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    2 ^ r.val.2.card *
          (2 * reducedCollisionWeight (m := m) r) + 2 ^ m ≤
      2 ^ r.val.2.card *
          (rootAndEscapeBlockedSignatureValueUnionWithUpper hh r).card +
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
  have hinter : ∀ C ∈ S, (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hsubset :=
    pow_card_mul_two_root_add_fullCube_le_covered_unionWithUpper_add_root
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
  simpa [hrootCard, hunionCard] using hsubset

/-- Numerical anchored-cube constraint forced by the enriched value union. -/
theorem pow_sourceTailCard_mul_two_weight_add_tailFace_le_fullCube_add_weight
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    2 ^ r.val.2.card *
          (2 * reducedCollisionWeight (m := m) r) + 2 ^ m ≤
      2 ^ r.val.2.card * 2 ^ m +
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
  have hinter : ∀ C ∈ S, (r.val.2 ∩ C).Nonempty := by
    intro C hC
    exact sourceTail_inter_escapeBlockedSignature_nonempty
      hg hh hh0 r hr hrmin hC
  have hsubset :=
    pow_card_mul_two_root_add_fullCube_le_scaled_fullCube_add_root
    R r.val.2 S hB hBR hcards hcover' hinter
  have hrootCard :
      (blockedSignatureSubsetLayer R).card =
        reducedCollisionWeight (m := m) r := by
    rw [← collisionPaddingSubsetLayer_eq_blockedSignatureSubsetLayer r,
      card_collisionPaddingSubsetLayer]
  simpa [hrootCard] using hsubset

end CriticalUpperFace

end MinModulus
