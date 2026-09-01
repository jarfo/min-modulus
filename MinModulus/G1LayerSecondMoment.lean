/-
# A second-moment lower bound for finite layer unions

The signature-indexed restored layers all have one common size and every
distinct pair overlaps in at most half that size.  This file supplies the
global combinatorial count needed to use those local facts simultaneously.

For a finite family `L_i`, the first moment of point multiplicities is the
sum of layer sizes and the second moment is the sum of all ordered pairwise
intersection sizes.  Cauchy--Schwarz then bounds the square of total
incidence mass by union size times intersection mass.  If all `k` layers have
size `w` and distinct pairs satisfy `2 |L_i ∩ L_j| ≤ w`, splitting the
diagonal from each row gives

`2 k w ≤ (k + 1) |⋃ L_i|`.

This tends to the sharp factor-two gain as the number of distinct layers
grows and is the first count using the whole restored family at once.
-/
import MinModulus.G1SignatureLayers
import Mathlib.Algebra.Order.Chebyshev

namespace MinModulus

open Finset

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- Number of layers in `F` containing a point. -/
def finsetFamilyMultiplicity (F : Finset ι) (L : ι → Finset α)
    (x : α) : ℕ :=
  (F.filter fun i ↦ x ∈ L i).card

omit [DecidableEq ι] in
/-- A multiplicity is a sum of membership indicators. -/
theorem finsetFamilyMultiplicity_eq_sum_boole
    (F : Finset ι) (L : ι → Finset α) (x : α) :
    finsetFamilyMultiplicity F L x =
      ∑ i ∈ F, if x ∈ L i then 1 else 0 := by
  classical
  unfold finsetFamilyMultiplicity
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

omit [DecidableEq ι] in
/-- First-moment double count for a finite family of finsets. -/
theorem sum_finsetFamilyMultiplicity_eq_sum_card
    (F : Finset ι) (L : ι → Finset α) :
    ∑ x ∈ F.biUnion L, finsetFamilyMultiplicity F L x =
      ∑ i ∈ F, (L i).card := by
  classical
  calc
    ∑ x ∈ F.biUnion L, finsetFamilyMultiplicity F L x =
        ∑ x ∈ F.biUnion L,
          ∑ i ∈ F, if x ∈ L i then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      exact finsetFamilyMultiplicity_eq_sum_boole F L x
    _ = ∑ i ∈ F, ∑ x ∈ F.biUnion L,
          if x ∈ L i then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ i ∈ F, (L i).card := by
      apply Finset.sum_congr rfl
      intro i hi
      have hsubset : L i ⊆ F.biUnion L :=
        Finset.subset_biUnion_of_mem L hi
      have hfilter : (F.biUnion L).filter (fun x ↦ x ∈ L i) = L i := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · exact fun hx ↦ hx.2
        · exact fun hx ↦ ⟨hsubset hx, hx⟩
      calc
        ∑ x ∈ F.biUnion L, (if x ∈ L i then 1 else 0) =
            ∑ x ∈ (F.biUnion L).filter (fun x ↦ x ∈ L i), 1 := by
          rw [Finset.sum_filter]
        _ = (L i).card := by rw [hfilter]; simp

omit [DecidableEq ι] in
/-- Second-moment double count: squared point multiplicities equal the sum
of all ordered pairwise intersection cardinalities. -/
theorem sum_sq_finsetFamilyMultiplicity_eq_sum_pair_inter
    (F : Finset ι) (L : ι → Finset α) :
    ∑ x ∈ F.biUnion L, (finsetFamilyMultiplicity F L x) ^ 2 =
      ∑ p ∈ F ×ˢ F, (L p.1 ∩ L p.2).card := by
  classical
  calc
    ∑ x ∈ F.biUnion L, (finsetFamilyMultiplicity F L x) ^ 2 =
        ∑ x ∈ F.biUnion L, ∑ p ∈ F ×ˢ F,
          if x ∈ L p.1 ∩ L p.2 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [finsetFamilyMultiplicity_eq_sum_boole]
      rw [pow_two, Finset.sum_product]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      by_cases hxi : x ∈ L i <;> by_cases hxj : x ∈ L j <;>
        simp [hxi, hxj]
    _ = ∑ p ∈ F ×ˢ F, ∑ x ∈ F.biUnion L,
          if x ∈ L p.1 ∩ L p.2 then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ p ∈ F ×ˢ F, (L p.1 ∩ L p.2).card := by
      apply Finset.sum_congr rfl
      intro p hp
      have hp' := Finset.mem_product.mp hp
      have hsubset : L p.1 ∩ L p.2 ⊆ F.biUnion L :=
        Finset.inter_subset_left.trans
          (Finset.subset_biUnion_of_mem L hp'.1)
      have hfilter : (F.biUnion L).filter
          (fun x ↦ x ∈ L p.1 ∩ L p.2) = L p.1 ∩ L p.2 := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · exact fun hx ↦ hx.2
        · exact fun hx ↦ ⟨hsubset hx, hx⟩
      calc
        ∑ x ∈ F.biUnion L,
            (if x ∈ L p.1 ∩ L p.2 then 1 else 0) =
          ∑ x ∈ (F.biUnion L).filter
            (fun x ↦ x ∈ L p.1 ∩ L p.2), 1 := by
            rw [Finset.sum_filter]
        _ = (L p.1 ∩ L p.2).card := by rw [hfilter]; simp

omit [DecidableEq ι] in
/-- Cauchy--Schwarz in finite-family form. -/
theorem square_sum_card_le_union_card_mul_sum_pair_inter
    (F : Finset ι) (L : ι → Finset α) :
    (∑ i ∈ F, (L i).card) ^ 2 ≤
      (F.biUnion L).card *
        ∑ p ∈ F ×ˢ F, (L p.1 ∩ L p.2).card := by
  classical
  have hcs := sq_sum_le_card_mul_sum_sq
    (s := F.biUnion L)
    (f := fun x ↦ finsetFamilyMultiplicity F L x)
  rw [sum_finsetFamilyMultiplicity_eq_sum_card,
    sum_sq_finsetFamilyMultiplicity_eq_sum_pair_inter] at hcs
  exact hcs

/-- Diagonal/off-diagonal split for an equal-size family with pairwise
half-overlap. -/
theorem two_mul_sum_pair_inter_le_card_mul_succ_mul
    (F : Finset ι) (L : ι → Finset α) (w : ℕ)
    (hcard : ∀ i ∈ F, (L i).card = w)
    (hinter : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      2 * (L i ∩ L j).card ≤ w) :
    2 * (∑ p ∈ F ×ˢ F, (L p.1 ∩ L p.2).card) ≤
      F.card * (F.card + 1) * w := by
  classical
  rw [Finset.sum_product]
  calc
    2 * (∑ i ∈ F, ∑ j ∈ F, (L i ∩ L j).card) =
        ∑ i ∈ F, 2 * (∑ j ∈ F, (L i ∩ L j).card) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ i ∈ F, (F.card + 1) * w := by
      apply Finset.sum_le_sum
      intro i hi
      have hdiag : (L i ∩ L i).card = w := by
        simpa using hcard i hi
      have hoff : 2 * (∑ j ∈ F.erase i,
          (L i ∩ L j).card) ≤ (F.erase i).card * w := by
        calc
          2 * (∑ j ∈ F.erase i, (L i ∩ L j).card) =
              ∑ j ∈ F.erase i, 2 * (L i ∩ L j).card := by
            rw [Finset.mul_sum]
          _ ≤ ∑ _j ∈ F.erase i, w := by
            apply Finset.sum_le_sum
            intro j hj
            have hj' := Finset.mem_erase.mp hj
            exact hinter i hi j hj'.2 hj'.1.symm
          _ = (F.erase i).card * w := by simp
      have hdecomp : (∑ j ∈ F, (L i ∩ L j).card) =
          (L i ∩ L i).card +
            ∑ j ∈ F.erase i, (L i ∩ L j).card :=
        (Finset.add_sum_erase F (fun j ↦ (L i ∩ L j).card) hi).symm
      rw [hdecomp, hdiag]
      calc
        2 * (w + ∑ j ∈ F.erase i, (L i ∩ L j).card) =
            2 * w + 2 * (∑ j ∈ F.erase i,
              (L i ∩ L j).card) := by ring
        _ ≤ 2 * w + (F.erase i).card * w :=
          Nat.add_le_add_left hoff _
        _ = (2 + (F.erase i).card) * w := by ring
        _ = (F.card + 1) * w := by
          rw [Finset.card_erase_of_mem hi]
          congr 1
          have hpos : 0 < F.card := Finset.card_pos.mpr ⟨i, hi⟩
          omega
    _ = F.card * ((F.card + 1) * w) := by simp
    _ = F.card * (F.card + 1) * w := by ring

/-- Global union lower bound for equal-size pairwise-half-overlapping layers. -/
theorem two_mul_card_mul_weight_le_succ_mul_familyUnion_card
    (F : Finset ι) (L : ι → Finset α) (w : ℕ)
    (hF : F.Nonempty) (hw : 0 < w)
    (hcard : ∀ i ∈ F, (L i).card = w)
    (hinter : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      2 * (L i ∩ L j).card ≤ w) :
    2 * F.card * w ≤ (F.card + 1) * (F.biUnion L).card := by
  classical
  have hsum : (∑ i ∈ F, (L i).card) = F.card * w :=
    Finset.sum_const_nat hcard
  have hcs := square_sum_card_le_union_card_mul_sum_pair_inter F L
  rw [hsum] at hcs
  have hpairs := two_mul_sum_pair_inter_le_card_mul_succ_mul
    F L w hcard hinter
  have hscaled : 2 * (F.card * w) ^ 2 ≤
      (F.biUnion L).card * (F.card * (F.card + 1) * w) := by
    calc
      2 * (F.card * w) ^ 2 ≤
          2 * ((F.biUnion L).card *
            ∑ p ∈ F ×ˢ F, (L p.1 ∩ L p.2).card) :=
        Nat.mul_le_mul_left 2 hcs
      _ = (F.biUnion L).card *
          (2 * ∑ p ∈ F ×ˢ F, (L p.1 ∩ L p.2).card) := by ring
      _ ≤ (F.biUnion L).card * (F.card * (F.card + 1) * w) :=
        Nat.mul_le_mul_left _ hpairs
  have hfactor : (F.card * w) * (2 * F.card * w) ≤
      (F.card * w) * ((F.card + 1) * (F.biUnion L).card) := by
    calc
      (F.card * w) * (2 * F.card * w) =
          2 * (F.card * w) ^ 2 := by ring
      _ ≤ (F.biUnion L).card * (F.card * (F.card + 1) * w) := hscaled
      _ = (F.card * w) *
          ((F.card + 1) * (F.biUnion L).card) := by ring
  exact Nat.le_of_mul_le_mul_left hfactor
    (Nat.mul_pos (Finset.card_pos.mpr hF) hw)

section SignatureLayers

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Index set consisting of the root layer and one intrinsic layer for every
distinct realized escape signature. -/
noncomputable def rootAndEscapeSignatureLayerIndices
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    Finset (Option (Finset (Fin m))) := by
  classical
  exact insert none <|
    (canonicalSupportEscapeBlockedSignatures hh r).image some

/-- Layer selected by an augmented index: `none` is the dominant root
padding layer and `some C` is the intrinsic layer of signature `C`. -/
noncomputable def rootAndEscapeSignatureLayer
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) :
    Option (Finset (Fin m)) → Finset G
  | none => collisionPaddingValueLayer r
  | some C => blockedSignatureValueLayer g C

@[simp] theorem none_mem_rootAndEscapeSignatureLayerIndices
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    none ∈ rootAndEscapeSignatureLayerIndices hh r := by
  classical
  simp [rootAndEscapeSignatureLayerIndices]

@[simp] theorem some_mem_rootAndEscapeSignatureLayerIndices_iff
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) {C : Finset (Fin m)} :
    some C ∈ rootAndEscapeSignatureLayerIndices hh r ↔
      C ∈ canonicalSupportEscapeBlockedSignatures hh r := by
  classical
  simp [rootAndEscapeSignatureLayerIndices]

/-- The augmented family has one more index than the distinct signature
family. -/
theorem card_rootAndEscapeSignatureLayerIndices
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (rootAndEscapeSignatureLayerIndices hh r).card =
      (canonicalSupportEscapeBlockedSignatures hh r).card + 1 := by
  classical
  rw [rootAndEscapeSignatureLayerIndices]
  have hnone : none ∉
      (canonicalSupportEscapeBlockedSignatures hh r).image some := by simp
  rw [Finset.card_insert_of_notMem hnone,
    Finset.card_image_of_injective _]
  intro C D hCD
  exact Option.some.inj hCD

/-- The abstract family union is exactly the previously defined root-plus-
signature value union. -/
theorem biUnion_rootAndEscapeSignatureLayerIndices
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (rootAndEscapeSignatureLayerIndices hh r).biUnion
        (rootAndEscapeSignatureLayer r) =
      rootAndEscapeBlockedSignatureValueUnion hh r := by
  classical
  ext x
  simp [rootAndEscapeSignatureLayerIndices, rootAndEscapeSignatureLayer,
    rootAndEscapeBlockedSignatureValueUnion,
    canonicalSupportEscapeBlockedSignatureValueUnion]

/-- Every layer in the augmented signature family has dominant weight. -/
theorem card_rootAndEscapeSignatureLayer_eq_rootWeight
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (i : Option (Finset (Fin m)))
    (hi : i ∈ rootAndEscapeSignatureLayerIndices hh r) :
    (rootAndEscapeSignatureLayer r i).card =
      reducedCollisionWeight (m := m) r := by
  cases i with
  | none =>
      simpa [rootAndEscapeSignatureLayer] using
        card_collisionPaddingValueLayer hg r
  | some C =>
      have hC : C ∈ canonicalSupportEscapeBlockedSignatures hh r :=
        (some_mem_rootAndEscapeSignatureLayerIndices_iff hh r).mp hi
      simpa [rootAndEscapeSignatureLayer] using
        card_escapeBlockedSignatureValueLayer_eq_rootWeight
          hg hh r hrmin hC

/-- Any two distinct layers in the augmented family overlap in at most half
of the dominant weight. -/
theorem two_mul_card_rootAndEscapeSignatureLayers_inter_le
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    (i : Option (Finset (Fin m)))
    (hi : i ∈ rootAndEscapeSignatureLayerIndices hh r)
    (j : Option (Finset (Fin m)))
    (hj : j ∈ rootAndEscapeSignatureLayerIndices hh r)
    (hij : i ≠ j) :
    2 * (rootAndEscapeSignatureLayer r i ∩
        rootAndEscapeSignatureLayer r j).card ≤
      reducedCollisionWeight (m := m) r := by
  cases i with
  | none =>
      cases j with
      | none => exact False.elim (hij rfl)
      | some D =>
          have hD : D ∈ canonicalSupportEscapeBlockedSignatures hh r :=
            (some_mem_rootAndEscapeSignatureLayerIndices_iff hh r).mp hj
          simpa [rootAndEscapeSignatureLayer, Finset.inter_comm] using
            two_mul_card_escapeBlockedSignatureValueLayer_inter_root_le
              hg hh r hr hmajor hD
  | some C =>
      have hC : C ∈ canonicalSupportEscapeBlockedSignatures hh r :=
        (some_mem_rootAndEscapeSignatureLayerIndices_iff hh r).mp hi
      cases j with
      | none =>
          simpa [rootAndEscapeSignatureLayer] using
            two_mul_card_escapeBlockedSignatureValueLayer_inter_root_le
              hg hh r hr hmajor hC
      | some D =>
          have hD : D ∈ canonicalSupportEscapeBlockedSignatures hh r :=
            (some_mem_rootAndEscapeSignatureLayerIndices_iff hh r).mp hj
          have hCD : C ≠ D := by
            intro h
            apply hij
            rw [h]
          simpa [rootAndEscapeSignatureLayer] using
            two_mul_card_escapeBlockedSignatureValueLayers_inter_le
              hg hh r hrmin hC hD hCD

/-- Second-moment lower bound for the complete multiplicity-free restored
family, including the dominant root layer. -/
theorem two_mul_signatureCount_succ_mul_weight_le
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (hh : h + h = 0) (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    2 * ((canonicalSupportEscapeBlockedSignatures hh r).card + 1) *
        reducedCollisionWeight (m := m) r ≤
      ((canonicalSupportEscapeBlockedSignatures hh r).card + 2) *
        (rootAndEscapeBlockedSignatureValueUnion hh r).card := by
  let F := rootAndEscapeSignatureLayerIndices hh r
  let L := rootAndEscapeSignatureLayer r
  have hF : F.Nonempty := by
    exact ⟨none, none_mem_rootAndEscapeSignatureLayerIndices hh r⟩
  have hw : 0 < reducedCollisionWeight (m := m) r := by
    simp [reducedCollisionWeight]
  have hbound := two_mul_card_mul_weight_le_succ_mul_familyUnion_card
    F L (reducedCollisionWeight (m := m) r) hF hw
      (card_rootAndEscapeSignatureLayer_eq_rootWeight hg hh r hrmin)
      (two_mul_card_rootAndEscapeSignatureLayers_inter_le
        hg hh r hr hrmin hmajor)
  rw [card_rootAndEscapeSignatureLayerIndices hh r,
    biUnion_rootAndEscapeSignatureLayerIndices hh r] at hbound
  simpa [Nat.add_assoc] using hbound

end SignatureLayers

end MinModulus
