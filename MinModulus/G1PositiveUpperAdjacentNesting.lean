/-
# Symmetric upper-face accounting: only adjacent nesting costs extra

The earlier ordered-pair budget charged every strict positive-tail nesting
twice.  Pairing `(q,u)` with `(u,q)` reveals the exact scale.

If `A_q ⊂ A_u` and `d = |A_u|-|A_q|`, then

  `|Upper(A_q)| = 2^d |Upper(A_u)|`.

The two ordered intersections contribute `4|Upper(A_u)|` after the factor two
in the second moment.  The ordinary ordered baseline already contributes
`|Upper(A_q)|+|Upper(A_u)|`.  Hence an extra face is needed only when `d=1`;
for `d≥2` the baseline has spare capacity.

This file formalizes the symmetric estimate and replaces the full nesting
mass by a single copy of the adjacent-nesting face mass.
-/
import MinModulus.G1PositiveUpperNestedCrowding

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Strict positive-tail nesting with cardinality gap exactly one. -/
noncomputable def reducedCollisionAdjacentPositiveNestingPairs
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) := by
  classical
  exact (reducedCollisionStrictPositiveNestingPairs F).filter (fun p ↦
    p.2.val.1.card = p.1.val.1.card + 1)

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionAdjacentPositiveNestingPairs_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ reducedCollisionAdjacentPositiveNestingPairs F ↔
      p ∈ reducedCollisionStrictPositiveNestingPairs F ∧
        p.2.val.1.card = p.1.val.1.card + 1 := by
  classical
  simp [reducedCollisionAdjacentPositiveNestingPairs]

/-- Face mass of the larger positive tail in adjacent nesting pairs. -/
noncomputable def reducedCollisionAdjacentPositiveNestingFaceMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) : ℕ := by
  classical
  exact (reducedCollisionAdjacentPositiveNestingPairs F).sum (fun p ↦
    (reducedCollisionPositiveUpperValueLayer p.2).card)

/-- Pointwise adjacent-nesting charge, before restricting to a family. -/
noncomputable def reducedCollisionAdjacentPositiveNestingCharge
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) : ℕ := by
  classical
  exact if q.val.1 ⊂ u.val.1 ∧
      u.val.1.card = q.val.1.card + 1 then
    (reducedCollisionPositiveUpperValueLayer u).card else 0

/-- A strict nested pair is paid by its two face baselines, except that a
cardinality-one step needs one extra copy of the smaller face. -/
theorem four_mul_positiveUpper_inter_le_faces_add_adjacent_of_strictSubset
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h)
    (hnest : q.val.1 ⊂ u.val.1) :
    4 * (reducedCollisionPositiveUpperValueLayer q ∩
        reducedCollisionPositiveUpperValueLayer u).card ≤
      (reducedCollisionPositiveUpperValueLayer q).card +
        (reducedCollisionPositiveUpperValueLayer u).card +
          reducedCollisionAdjacentPositiveNestingCharge q u := by
  have hinter := blockedSignatureUpperValueLayers_inter_eq_right_of_subset
    (g := g) hnest.1
  have hqle : q.val.1.card ≤ m := by
    simpa using Finset.card_le_univ q.val.1
  have hule : u.val.1.card ≤ m := by
    simpa using Finset.card_le_univ u.val.1
  have hcardlt := Finset.card_lt_card hnest
  have hinter' :
      reducedCollisionPositiveUpperValueLayer q ∩
          reducedCollisionPositiveUpperValueLayer u =
        reducedCollisionPositiveUpperValueLayer u := by
    simpa [reducedCollisionPositiveUpperValueLayer] using hinter
  by_cases hadj : u.val.1.card = q.val.1.card + 1
  · have hexponent : m - q.val.1.card = (m - u.val.1.card) + 1 := by
      omega
    have hdouble :
        (reducedCollisionPositiveUpperValueLayer q).card =
          2 * (reducedCollisionPositiveUpperValueLayer u).card := by
      rw [reducedCollisionPositiveUpperValueLayer,
        reducedCollisionPositiveUpperValueLayer,
        card_blockedSignatureUpperValueLayer hg,
        card_blockedSignatureUpperValueLayer hg, hexponent, pow_succ]
      ring
    rw [hinter']
    simp [reducedCollisionAdjacentPositiveNestingCharge, hnest, hadj]
    omega
  · have hgap : q.val.1.card + 2 ≤ u.val.1.card := by omega
    have hexponent :
        (m - u.val.1.card) + 2 ≤ m - q.val.1.card := by omega
    have hpow := Nat.pow_le_pow_right
      (by norm_num : 0 < (2 : ℕ)) hexponent
    have hfour :
        4 * (reducedCollisionPositiveUpperValueLayer u).card ≤
          (reducedCollisionPositiveUpperValueLayer q).card := by
      rw [reducedCollisionPositiveUpperValueLayer,
        reducedCollisionPositiveUpperValueLayer,
        card_blockedSignatureUpperValueLayer hg,
        card_blockedSignatureUpperValueLayer hg]
      simpa [pow_add, Nat.mul_comm, Nat.mul_left_comm,
        Nat.mul_assoc] using hpow
    rw [hinter']
    simp [reducedCollisionAdjacentPositiveNestingCharge, hnest, hadj]
    omega

/-- Symmetric local estimate.  Diagonal pairs cost one extra face; among
distinct pairs, only adjacent strict nesting costs one extra smaller face. -/
theorem four_mul_positiveUpper_inter_le_two_faces_add_diagonal_adjacent
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h) :
    4 * (reducedCollisionPositiveUpperValueLayer q ∩
        reducedCollisionPositiveUpperValueLayer u).card ≤
      (reducedCollisionPositiveUpperValueLayer q).card +
        (reducedCollisionPositiveUpperValueLayer u).card +
        2 * reducedCollisionPositiveUpperDiagonalCharge q u +
        reducedCollisionAdjacentPositiveNestingCharge q u +
        reducedCollisionAdjacentPositiveNestingCharge u q := by
  classical
  by_cases hqu : q = u
  · subst u
    simp [reducedCollisionPositiveUpperDiagonalCharge,
      reducedCollisionAdjacentPositiveNestingCharge]
    omega
  have hleft : q.val.1 ≠ u.val.1 := by
    intro hEq
    exact hqu (reducedSubsetSumCollision_eq_of_left_eq hg q u hEq)
  by_cases hsub : q.val.1 ⊆ u.val.1
  · have hnest : q.val.1 ⊂ u.val.1 :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hleft⟩
    have hnreverse : ¬u.val.1 ⊂ q.val.1 := fun hr ↦ hr.2 hsub
    have hbound :=
      four_mul_positiveUpper_inter_le_faces_add_adjacent_of_strictSubset
        hg q u hnest
    simpa [reducedCollisionPositiveUpperDiagonalCharge,
      reducedCollisionAdjacentPositiveNestingCharge,
      hqu, hnest, hnreverse] using hbound
  by_cases husub : u.val.1 ⊆ q.val.1
  · have hnest : u.val.1 ⊂ q.val.1 :=
      Finset.ssubset_iff_subset_ne.mpr ⟨husub, Ne.symm hleft⟩
    have hnforward : ¬q.val.1 ⊂ u.val.1 := fun hf ↦ hsub hf.1
    have hbound :=
      four_mul_positiveUpper_inter_le_faces_add_adjacent_of_strictSubset
        hg u q hnest
    simpa [Finset.inter_comm, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc, reducedCollisionPositiveUpperDiagonalCharge,
      reducedCollisionAdjacentPositiveNestingCharge,
      hqu, Ne.symm hqu, hnest, hnforward] using hbound
  · have hnforward : ¬q.val.1 ⊂ u.val.1 := fun hf ↦ hsub hf.1
    have hnreverse : ¬u.val.1 ⊂ q.val.1 := fun hr ↦ husub hr.1
    rcases le_total q.val.1.card u.val.1.card with hcard | hcard
    · have hinter :=
        two_mul_card_blockedSignatureUpperValueLayers_inter_le_of_not_subset
          hg q.val.1 u.val.1 hsub
      have hface :
          (reducedCollisionPositiveUpperValueLayer u).card ≤
            (reducedCollisionPositiveUpperValueLayer q).card := by
        rw [reducedCollisionPositiveUpperValueLayer,
          reducedCollisionPositiveUpperValueLayer,
          card_blockedSignatureUpperValueLayer hg,
          card_blockedSignatureUpperValueLayer hg]
        exact Nat.pow_le_pow_right (by norm_num)
          (Nat.sub_le_sub_left hcard m)
      change 2 *
          (reducedCollisionPositiveUpperValueLayer q ∩
            reducedCollisionPositiveUpperValueLayer u).card ≤
        (reducedCollisionPositiveUpperValueLayer u).card at hinter
      simp [reducedCollisionPositiveUpperDiagonalCharge,
        reducedCollisionAdjacentPositiveNestingCharge,
        hqu, hnforward, hnreverse]
      omega
    · have hinter :=
        two_mul_card_blockedSignatureUpperValueLayers_inter_le_of_not_subset
          hg u.val.1 q.val.1 husub
      have hface :
          (reducedCollisionPositiveUpperValueLayer q).card ≤
            (reducedCollisionPositiveUpperValueLayer u).card := by
        rw [reducedCollisionPositiveUpperValueLayer,
          reducedCollisionPositiveUpperValueLayer,
          card_blockedSignatureUpperValueLayer hg,
          card_blockedSignatureUpperValueLayer hg]
        exact Nat.pow_le_pow_right (by norm_num)
          (Nat.sub_le_sub_left hcard m)
      change 2 *
          (reducedCollisionPositiveUpperValueLayer u ∩
            reducedCollisionPositiveUpperValueLayer q).card ≤
        (reducedCollisionPositiveUpperValueLayer q).card at hinter
      simp [reducedCollisionPositiveUpperDiagonalCharge,
        reducedCollisionAdjacentPositiveNestingCharge,
        hqu, hnforward, hnreverse]
      rw [Finset.inter_comm] at hinter
      omega

/-- Exact sum of the pointwise adjacent charges over a family. -/
theorem sum_adjacentPositiveNestingCharge_eq_faceMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    (F ×ˢ F).sum (fun p ↦
        reducedCollisionAdjacentPositiveNestingCharge p.1 p.2) =
      reducedCollisionAdjacentPositiveNestingFaceMass F := by
  classical
  rw [reducedCollisionAdjacentPositiveNestingFaceMass,
    reducedCollisionAdjacentPositiveNestingPairs,
    reducedCollisionStrictPositiveNestingPairs,
    Finset.sum_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hnest : p.1.val.1 ⊂ p.2.val.1
  · by_cases hadj : p.2.val.1.card = p.1.val.1.card + 1
    · simp [reducedCollisionAdjacentPositiveNestingCharge, hnest, hadj]
    · simp [reducedCollisionAdjacentPositiveNestingCharge, hnest, hadj]
  · simp [reducedCollisionAdjacentPositiveNestingCharge, hnest]

/-- Sharp all-family ordered-intersection budget: deep nesting is free, and
adjacent nesting is charged only once. -/
theorem two_mul_sum_positiveUpper_pairInter_le_card_mul_incidence_add_diagonal_add_adjacent
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    2 * (F ×ˢ F).sum (fun p ↦
        (reducedCollisionPositiveUpperValueLayer p.1 ∩
          reducedCollisionPositiveUpperValueLayer p.2).card) ≤
      F.card * reducedCollisionPositiveUpperIncidenceMass F +
        reducedCollisionPositiveUpperIncidenceMass F +
        reducedCollisionAdjacentPositiveNestingFaceMass F := by
  classical
  let I : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    (reducedCollisionPositiveUpperValueLayer p.1 ∩
      reducedCollisionPositiveUpperValueLayer p.2).card
  let face : ReducedSubsetSumCollision g h → ℕ := fun q ↦
    (reducedCollisionPositiveUpperValueLayer q).card
  have hsum :
      4 * (F ×ˢ F).sum I ≤
        2 * (F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F) := by
    have hlocal :
        (F ×ˢ F).sum (fun p ↦ 4 * I p) ≤
          (F ×ˢ F).sum (fun p ↦
            face p.1 + face p.2 +
              2 * reducedCollisionPositiveUpperDiagonalCharge p.1 p.2 +
              reducedCollisionAdjacentPositiveNestingCharge p.1 p.2 +
              reducedCollisionAdjacentPositiveNestingCharge p.2 p.1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact four_mul_positiveUpper_inter_le_two_faces_add_diagonal_adjacent
        hg p.1 p.2
    have hfirst : (F ×ˢ F).sum (fun p ↦ face p.1) =
        F.card * reducedCollisionPositiveUpperIncidenceMass F := by
      rw [Finset.sum_product]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [reducedCollisionPositiveUpperIncidenceMass, Finset.mul_sum]
      rfl
    have hsecond : (F ×ˢ F).sum (fun p ↦ face p.2) =
        F.card * reducedCollisionPositiveUpperIncidenceMass F := by
      rw [Finset.sum_product, Finset.sum_comm]
      rw [Finset.sum_product] at hfirst
      simpa only [Prod.fst, Prod.snd] using hfirst
    have hdiag : (F ×ˢ F).sum (fun p ↦
        reducedCollisionPositiveUpperDiagonalCharge p.1 p.2) =
        reducedCollisionPositiveUpperIncidenceMass F := by
      rw [Finset.sum_product]
      simp [reducedCollisionPositiveUpperDiagonalCharge,
        reducedCollisionPositiveUpperIncidenceMass,
        reducedCollisionPositiveUpperValueLayer]
    have hadj := sum_adjacentPositiveNestingCharge_eq_faceMass F
    have hadjReverse : (F ×ˢ F).sum (fun p ↦
        reducedCollisionAdjacentPositiveNestingCharge p.2 p.1) =
        reducedCollisionAdjacentPositiveNestingFaceMass F := by
      rw [Finset.sum_product, Finset.sum_comm]
      rw [Finset.sum_product] at hadj
      simpa only [Prod.fst, Prod.snd] using hadj
    rw [← Finset.mul_sum] at hlocal
    calc
      4 * (F ×ˢ F).sum I ≤
          (F ×ˢ F).sum (fun p ↦
            face p.1 + face p.2 +
              2 * reducedCollisionPositiveUpperDiagonalCharge p.1 p.2 +
              reducedCollisionAdjacentPositiveNestingCharge p.1 p.2 +
              reducedCollisionAdjacentPositiveNestingCharge p.2 p.1) := hlocal
      _ = 2 * (F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib,
          hfirst, hsecond, ← Finset.mul_sum, hdiag, hadj, hadjReverse]
        ring
  have hfactor :
      2 * (2 * (F ×ˢ F).sum I) ≤
        2 * (F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F) := by
    calc
      2 * (2 * (F ×ˢ F).sum I) =
          4 * (F ×ˢ F).sum I := by ring
      _ ≤ 2 * (F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F) := hsum
  exact Nat.le_of_mul_le_mul_left hfactor (by norm_num)

/-- Second moment with the sharp adjacent-nesting budget. -/
theorem two_mul_positiveUpperIncidenceMass_sq_le_union_mul_adjacentNestingBudget
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    2 * (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll F).card *
        (F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F) := by
  classical
  let L : ReducedSubsetSumCollision g h → Finset G :=
    reducedCollisionPositiveUpperValueLayer
  have hcs := square_sum_card_le_union_card_mul_sum_pair_inter F L
  have hpairs :=
    two_mul_sum_positiveUpper_pairInter_le_card_mul_incidence_add_diagonal_add_adjacent
      hg F
  change (F.sum fun q ↦ (L q).card) ^ 2 ≤
    (F.biUnion L).card *
      (F ×ˢ F).sum (fun p ↦ (L p.1 ∩ L p.2).card) at hcs
  change 2 * (F ×ˢ F).sum (fun p ↦ (L p.1 ∩ L p.2).card) ≤
    F.card * reducedCollisionPositiveUpperIncidenceMass F +
      reducedCollisionPositiveUpperIncidenceMass F +
      reducedCollisionAdjacentPositiveNestingFaceMass F at hpairs
  change 2 * (F.sum fun q ↦ (L q).card) ^ 2 ≤
    (F.biUnion L).card *
      (F.card * reducedCollisionPositiveUpperIncidenceMass F +
        reducedCollisionPositiveUpperIncidenceMass F +
        reducedCollisionAdjacentPositiveNestingFaceMass F)
  calc
    2 * (F.sum fun q ↦ (L q).card) ^ 2 ≤
        2 * ((F.biUnion L).card *
          (F ×ˢ F).sum (fun p ↦ (L p.1 ∩ L p.2).card)) :=
      Nat.mul_le_mul_left 2 hcs
    _ = (F.biUnion L).card *
        (2 * (F ×ˢ F).sum (fun p ↦
          (L p.1 ∩ L p.2).card)) := by ring
    _ ≤ (F.biUnion L).card *
        (F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F) :=
      Nat.mul_le_mul_left _ hpairs

/-- Factor-eight large-support supply with only one copy of adjacent-nesting
face mass left in the second-moment budget. -/
theorem oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentNestingBudget
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    128 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll F).card *
        (F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F) := by
  have hmass := eight_mul_sum_weight_le_positiveUpperIncidenceMass
    hg F hcanonical hsix
  have hsq' := Nat.mul_le_mul hmass hmass
  have hsq : (8 * F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
      (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 := by
    simpa [pow_two] using hsq'
  have hsecond :=
    two_mul_positiveUpperIncidenceMass_sq_le_union_mul_adjacentNestingBudget
      hg F
  calc
    128 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 =
        2 * (8 * F.sum (reducedCollisionWeight (m := m))) ^ 2 := by ring
    _ ≤ 2 * (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 :=
      Nat.mul_le_mul_left 2 hsq
    _ ≤ (reducedCollisionPositiveUpperValueUnionAll F).card *
        (F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F) := hsecond

section CriticalAdjacentNesting

/-- Milestone 2cy: symmetric accounting for the complete non-root family
removes every nesting gap of at least two and leaves only one copy of the
adjacent-nesting face mass. -/
theorem genuineDominant_liveRoot_largeSupport_positiveUpper_adjacentNesting
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    2 * (F ×ˢ F).sum (fun p ↦
        (reducedCollisionPositiveUpperValueLayer p.1 ∩
          reducedCollisionPositiveUpperValueLayer p.2).card) ≤
        F.card * reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionPositiveUpperIncidenceMass F +
          reducedCollisionAdjacentPositiveNestingFaceMass F ∧
      128 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll F).card *
          (F.card * reducedCollisionPositiveUpperIncidenceMass F +
            reducedCollisionPositiveUpperIncidenceMass F +
            reducedCollisionAdjacentPositiveNestingFaceMass F) ∧
      (reducedCollisionPositiveUpperValueUnionAll F).card ≤ 2 ^ n := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
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
    have hvcanonical : v ∈ canonicalReducedCollisions (g := g)
        (half_add_half (show 2 ^ (s + 1) * q = 2 * (2 ^ s * q) by
          rw [pow_succ]
          ring)) := by
      simpa [criticalCanonicalReducedCollisions] using (hmem v hv).1
    exact canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp hvcanonical)
  have hsix : ∀ v ∈ F, 6 ≤ (reducedCollisionSupport v).card := by
    intro v hv
    exact genuineDominant_liveRoot_all_other_support_card_six_le
      hqodd g hg r hr hres hAcard hBcard v
        (hmem v hv).1 (hmem v hv).2
  refine ⟨
    two_mul_sum_positiveUpper_pairInter_le_card_mul_incidence_add_diagonal_add_adjacent
      hg F,
    oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentNestingBudget
      hg F hcanonical hsix,
    ?_⟩
  calc
    (reducedCollisionPositiveUpperValueUnionAll F).card ≤
        (subsetSumRange g).card := Finset.card_le_card
          (reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange F)
    _ = 2 ^ n := card_subsetSumRange g hg

end CriticalAdjacentNesting

end MinModulus
