/-
# Cross-stratum nesting for positive upper faces

`G1LargeSupportUpperFacePacking` controls all positive upper faces having the
same forced-set cardinality.  Across different cardinalities there is one
new phenomenon: if `C ⊂ D`, then the upper face forcing `D` is contained in
the upper face forcing `C`, so the smaller face is duplicated completely.

This file proves that nesting is the only such loss.  If neither forced set
contains the other, the two upper faces intersect in at most half of the
smaller face.  Summing the pointwise dichotomy gives a single second-moment
bound for the whole large-support family, with an explicit pair-duplication
term supported only on equal indices or nested positive tails.

Combining this with the factor-eight incidence supply from milestone 2ct
gives

  `128 W^2 ≤ |U| * PairBudget`,

where `W` is the complete non-root padding weight and `U` is the union of all
positive upper faces.  The remaining cross-stratum obstruction is therefore
precisely strict positive-tail nesting, rather than arbitrary face overlap.
-/
import MinModulus.G1LargeSupportUpperFacePacking

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Forcing a larger coordinate set gives a smaller upper face. -/
theorem blockedSignatureUpperValueLayer_mono
    {g : Fin (m + 1) → G}
    {C D : Finset (Fin m)} (hCD : C ⊆ D) :
    blockedSignatureUpperValueLayer g D ⊆
      blockedSignatureUpperValueLayer g C := by
  classical
  intro x hx
  rw [blockedSignatureUpperValueLayer] at hx ⊢
  rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
  apply Finset.mem_image.mpr
  exact ⟨S, mem_blockedSignatureUpperSubsetLayer_iff.mpr
    (hCD.trans (mem_blockedSignatureUpperSubsetLayer_iff.mp hS)), rfl⟩

/-- Nested forced sets give complete duplication of the smaller upper face. -/
theorem blockedSignatureUpperValueLayers_inter_eq_right_of_subset
    {g : Fin (m + 1) → G}
    {C D : Finset (Fin m)} (hCD : C ⊆ D) :
    blockedSignatureUpperValueLayer g C ∩
        blockedSignatureUpperValueLayer g D =
      blockedSignatureUpperValueLayer g D := by
  exact Finset.inter_eq_right.mpr
    (blockedSignatureUpperValueLayer_mono hCD)

/-- If `C` is no larger than `D` but is not contained in it, the two upper
faces meet in at most half of the smaller `D`-face. -/
theorem two_mul_card_blockedSignatureUpperValueLayers_inter_le_of_not_subset
    {g : Fin (m + 1) → G} (hg : ValidTuple g)
    (C D : Finset (Fin m))
    (hnsub : ¬C ⊆ D) :
    2 * (blockedSignatureUpperValueLayer g C ∩
        blockedSignatureUpperValueLayer g D).card ≤
      (blockedSignatureUpperValueLayer g D).card := by
  have hproper : D ⊂ C ∪ D := by
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.subset_union_right, ?_⟩
    intro heq
    apply hnsub
    intro x hxC
    have hx : x ∈ C ∪ D := Finset.mem_union_left _ hxC
    rwa [← heq] at hx
  have hstep : D.card + 1 ≤ (C ∪ D).card := by
    have := Finset.card_lt_card hproper
    omega
  have hunionLe : (C ∪ D).card ≤ m := by
    simpa using Finset.card_le_univ (C ∪ D)
  have hexponent : m - (C ∪ D).card + 1 ≤ m - D.card := by omega
  have hpow := Nat.pow_le_pow_right
    (by norm_num : 0 < (2 : ℕ)) hexponent
  have hinterCard :
      (blockedSignatureUpperValueLayer g C ∩
        blockedSignatureUpperValueLayer g D).card =
          2 ^ (m - (C ∪ D).card) := by
    rw [blockedSignatureUpperValueLayer,
      blockedSignatureUpperValueLayer,
      image_inter_eq_image_inter_of_injective
        (ssum g) (ssum_injective g hg),
      Finset.card_image_of_injective _ (ssum_injective g hg),
      blockedSignatureUpperSubsetLayers_inter,
      card_blockedSignatureUpperSubsetLayer,
      card_blockedSignatureSubsetLayer]
  rw [hinterCard, card_blockedSignatureUpperValueLayer hg]
  simpa [pow_succ, Nat.mul_comm] using hpow

/-- One collision's positive upper value face. -/
noncomputable def reducedCollisionPositiveUpperValueLayer
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) : Finset G :=
  blockedSignatureUpperValueLayer g q.val.1

/-- Union of positive upper faces over a complete reduced-collision family. -/
noncomputable def reducedCollisionPositiveUpperValueUnionAll
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) : Finset G := by
  classical
  exact F.biUnion reducedCollisionPositiveUpperValueLayer

/-- Extra pairwise duplication beyond the asymmetric half-overlap baseline.
It is nonzero only on the diagonal or when one positive tail contains the
other. -/
noncomputable def reducedCollisionPositiveUpperPairDuplication
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) : ℕ := by
  classical
  exact if q = u then
    (reducedCollisionPositiveUpperValueLayer q).card
  else if q.val.1 ⊆ u.val.1 then
    (reducedCollisionPositiveUpperValueLayer u).card
  else if u.val.1 ⊆ q.val.1 then
    (reducedCollisionPositiveUpperValueLayer q).card
  else 0

/-- The all-family pair budget: every ordered pair pays the first face once,
plus exactly the diagonal/nesting duplication above. -/
noncomputable def reducedCollisionPositiveUpperPairBudget
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) : ℕ := by
  classical
  exact (F ×ˢ F).sum (fun p ↦
    (reducedCollisionPositiveUpperValueLayer p.1).card +
      reducedCollisionPositiveUpperPairDuplication p.1 p.2)

/-- Local cross-stratum classification in the form needed for summation. -/
theorem two_mul_positiveUpper_inter_le_card_add_pairDuplication
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h) :
    2 * (reducedCollisionPositiveUpperValueLayer q ∩
        reducedCollisionPositiveUpperValueLayer u).card ≤
      (reducedCollisionPositiveUpperValueLayer q).card +
        reducedCollisionPositiveUpperPairDuplication q u := by
  classical
  by_cases hqu : q = u
  · subst u
    simp [reducedCollisionPositiveUpperPairDuplication,
      reducedCollisionPositiveUpperValueLayer, two_mul]
  by_cases hsub : q.val.1 ⊆ u.val.1
  · have hmono := blockedSignatureUpperValueLayer_mono
      (g := g) hsub
    have hinter := blockedSignatureUpperValueLayers_inter_eq_right_of_subset
      (g := g) hsub
    have hcardle := Finset.card_le_card hmono
    rw [reducedCollisionPositiveUpperValueLayer,
      reducedCollisionPositiveUpperValueLayer, hinter]
    simp only [reducedCollisionPositiveUpperPairDuplication,
      hqu, hsub, ↓reduceIte,
      reducedCollisionPositiveUpperValueLayer]
    omega
  by_cases husub : u.val.1 ⊆ q.val.1
  · have hinter := blockedSignatureUpperValueLayers_inter_eq_right_of_subset
      (g := g) husub
    rw [Finset.inter_comm,
      reducedCollisionPositiveUpperValueLayer,
      reducedCollisionPositiveUpperValueLayer, hinter]
    simp [reducedCollisionPositiveUpperPairDuplication,
      reducedCollisionPositiveUpperValueLayer, hqu, hsub, husub, two_mul]
  · have hhalf : 2 *
        (blockedSignatureUpperValueLayer g q.val.1 ∩
          blockedSignatureUpperValueLayer g u.val.1).card ≤
        (blockedSignatureUpperValueLayer g q.val.1).card := by
      rcases le_total q.val.1.card u.val.1.card with hcard | hcard
      · have hsmall :=
          two_mul_card_blockedSignatureUpperValueLayers_inter_le_of_not_subset
            hg q.val.1 u.val.1 hsub
        have hface :
            (blockedSignatureUpperValueLayer g u.val.1).card ≤
              (blockedSignatureUpperValueLayer g q.val.1).card := by
          rw [card_blockedSignatureUpperValueLayer hg,
            card_blockedSignatureUpperValueLayer hg]
          exact Nat.pow_le_pow_right (by norm_num)
            (Nat.sub_le_sub_left hcard m)
        exact hsmall.trans hface
      · simpa [Finset.inter_comm] using
          two_mul_card_blockedSignatureUpperValueLayers_inter_le_of_not_subset
            hg u.val.1 q.val.1 husub
    simpa [reducedCollisionPositiveUpperValueLayer,
      reducedCollisionPositiveUpperPairDuplication,
      hqu, hsub, husub] using hhalf

/-- Summed pairwise intersection mass is bounded by the explicit all-family
pair budget. -/
theorem two_mul_sum_positiveUpper_pairInter_le_pairBudget
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    2 * (F ×ˢ F).sum (fun p ↦
        (reducedCollisionPositiveUpperValueLayer p.1 ∩
          reducedCollisionPositiveUpperValueLayer p.2).card) ≤
      reducedCollisionPositiveUpperPairBudget F := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p hp
  exact two_mul_positiveUpper_inter_le_card_add_pairDuplication
    hg p.1 p.2

/-- All-family second moment with cross-stratum nesting isolated in the pair
budget. -/
theorem two_mul_positiveUpperIncidenceMass_sq_le_union_mul_pairBudget
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    2 * (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll F).card *
        reducedCollisionPositiveUpperPairBudget F := by
  classical
  let L : ReducedSubsetSumCollision g h → Finset G :=
    reducedCollisionPositiveUpperValueLayer
  have hcs := square_sum_card_le_union_card_mul_sum_pair_inter F L
  have hpairs := two_mul_sum_positiveUpper_pairInter_le_pairBudget hg F
  change (F.sum fun q ↦ (L q).card) ^ 2 ≤
    (F.biUnion L).card *
      (F ×ˢ F).sum (fun p ↦ (L p.1 ∩ L p.2).card) at hcs
  change 2 * (F ×ˢ F).sum (fun p ↦ (L p.1 ∩ L p.2).card) ≤
    reducedCollisionPositiveUpperPairBudget F at hpairs
  change 2 * (F.sum fun q ↦ (L q).card) ^ 2 ≤
    (F.biUnion L).card * reducedCollisionPositiveUpperPairBudget F
  calc
    2 * (F.sum fun q ↦ (L q).card) ^ 2 ≤
        2 * ((F.biUnion L).card *
          (F ×ˢ F).sum (fun p ↦ (L p.1 ∩ L p.2).card)) :=
      Nat.mul_le_mul_left 2 hcs
    _ = (F.biUnion L).card *
        (2 * (F ×ˢ F).sum (fun p ↦
          (L p.1 ∩ L p.2).card)) := by ring
    _ ≤ (F.biUnion L).card *
        reducedCollisionPositiveUpperPairBudget F :=
      Nat.mul_le_mul_left _ hpairs

/-- The large-support factor-eight supply turns the all-family second moment
into a quadratic padding-weight packing bound. -/
theorem oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_pairBudget
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    128 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll F).card *
        reducedCollisionPositiveUpperPairBudget F := by
  have hmass := eight_mul_sum_weight_le_positiveUpperIncidenceMass
    hg F hcanonical hsix
  have hsq' := Nat.mul_le_mul hmass hmass
  have hsq : (8 * F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
      (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 := by
    simpa [pow_two] using hsq'
  have hsecond :=
    two_mul_positiveUpperIncidenceMass_sq_le_union_mul_pairBudget hg F
  calc
    128 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 =
        2 * (8 * F.sum (reducedCollisionWeight (m := m))) ^ 2 := by ring
    _ ≤ 2 * (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 :=
      Nat.mul_le_mul_left 2 hsq
    _ ≤ (reducedCollisionPositiveUpperValueUnionAll F).card *
        reducedCollisionPositiveUpperPairBudget F := hsecond

/-- The complete positive-upper union lies in the anchored subset-sum cube. -/
theorem reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionPositiveUpperValueUnionAll F ⊆ subsetSumRange g := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨q, hq, hxq⟩
  rw [reducedCollisionPositiveUpperValueLayer,
    blockedSignatureUpperValueLayer] at hxq
  rcases Finset.mem_image.mp hxq with ⟨S, hS, rfl⟩
  rw [subsetSumRange]
  exact Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩

section CriticalNesting

/-- Milestone 2cu: all positive-cardinality strata from 2ct combine into one
upper-face union.  The sole cross-stratum loss is the explicit diagonal or
positive-tail-nesting duplication in `PairBudget`. -/
theorem genuineDominant_liveRoot_largeSupport_positiveUpper_allFamily
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    128 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll F).card *
          reducedCollisionPositiveUpperPairBudget F ∧
      (reducedCollisionPositiveUpperValueUnionAll F).card ≤ 2 ^ n := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  let F := criticalCanonicalNonrootCollisions g r
  have hmem : ∀ v ∈ F,
      v ∈ criticalCanonicalReducedCollisions g ∧ v ≠ r := by
    intro v hv
    have hv' : v ∈ (criticalCanonicalReducedCollisions g).erase r := by
      simpa [F, criticalCanonicalNonrootCollisions] using hv
    have hv'' := Finset.mem_erase.mp hv'
    exact ⟨hv''.2, hv''.1⟩
  have hcanonical : ∀ v ∈ F, v.val.1.card ≤ v.val.2.card := by
    intro v hv
    have hvcritical := (hmem v hv).1
    have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using hvcritical
    exact canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp hvcanonical)
  have hsix : ∀ v ∈ F, 6 ≤ (reducedCollisionSupport v).card := by
    intro v hv
    exact genuineDominant_liveRoot_all_other_support_card_six_le
      hqodd g hg r hr hres hAcard hBcard v
        (hmem v hv).1 (hmem v hv).2
  constructor
  · exact
      oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_pairBudget
        hg F hcanonical hsix
  · calc
      (reducedCollisionPositiveUpperValueUnionAll F).card ≤
          (subsetSumRange g).card := Finset.card_le_card
            (reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange F)
      _ = 2 ^ n := card_subsetSumRange g hg

end CriticalNesting

end MinModulus
