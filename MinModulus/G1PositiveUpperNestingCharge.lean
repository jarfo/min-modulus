/-
# Charging strict positive-tail nesting to canonical crossings

`G1PositiveUpperNesting` shows that the only excess overlap between positive
upper faces is caused by comparable positive tails.  This file identifies
that error with an already forced piece of the canonical crossing geometry.

If `A_q ⊂ A_u`, the crossing from `A_q` to `B_u` is impossible because
`A_q ⊆ A_u` and `A_u` is disjoint from `B_u`.  Pairwise canonical crossing
therefore forces the reverse crossing `A_u ∩ B_q ≠ ∅`.  Swapping a strict
nesting pair consequently injects it into the oriented canonical crossing
relation.

The pair budget from the previous module then has the exact decomposition

  `PairBudget = (|F|+1) * IncidenceMass + 2 * NestingFaceMass`.

Thus strict nesting is not a new combinatorial relation: its full face-weighted
cost is bounded by an oriented canonical-crossing face mass.
-/
import MinModulus.G1PositiveUpperNesting

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Ordered pairs whose first positive tail is strictly contained in the
second. -/
noncomputable def reducedCollisionStrictPositiveNestingPairs
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    Finset (ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h) := by
  classical
  exact (F ×ˢ F).filter (fun p ↦ p.1.val.1 ⊂ p.2.val.1)

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionStrictPositiveNestingPairs_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h} :
    p ∈ reducedCollisionStrictPositiveNestingPairs F ↔
      p.1 ∈ F ∧ p.2 ∈ F ∧ p.1.val.1 ⊂ p.2.val.1 := by
  classical
  simp [reducedCollisionStrictPositiveNestingPairs, and_assoc]

/-- Total smaller-face cost of the strictly nested ordered pairs. -/
noncomputable def reducedCollisionPositiveUpperNestingFaceMass
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) : ℕ := by
  classical
  exact (reducedCollisionStrictPositiveNestingPairs F).sum (fun p ↦
    (reducedCollisionPositiveUpperValueLayer p.2).card)

/-- Face-weighted oriented canonical crossing mass.  Unlike the earlier
product-weight crossing mass, this is normalized to the positive upper face
of the crossing source. -/
noncomputable def canonicalPositiveNegativeCrossFaceMass
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) : ℕ := by
  classical
  exact (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
    (reducedCollisionPositiveUpperValueLayer p.1).card)

/-- A strict inclusion `A_q ⊂ A_u` forces the canonical crossing in the
reverse orientation `(u,q)`. -/
theorem strictPositiveNesting_forces_reverse_canonicalCross
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (q u : ReducedSubsetSumCollision g h)
    (hq : q ∈ canonicalReducedCollisions (g := g) hh)
    (hu : u ∈ canonicalReducedCollisions (g := g) hh)
    (hnest : q.val.1 ⊂ u.val.1) :
    (u, q) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh := by
  have hqu : q ≠ u := by
    intro hEq
    subst u
    exact hnest.2 Finset.Subset.rfl
  have hcross := distinct_canonicalReducedCollisions_positive_negative_cross
    g hg hh hh0 q u
      (mem_canonicalReducedCollisions_iff.mp hq)
      (mem_canonicalReducedCollisions_iff.mp hu) (Ne.symm hqu)
  have hforward : ¬(q.val.1 ∩ u.val.2).Nonempty := by
    rintro ⟨j, hj⟩
    have hj' := Finset.mem_inter.mp hj
    exact Finset.disjoint_left.mp u.property.1
      (hnest.1 hj'.1) hj'.2
  have hreverse := hcross.resolve_left hforward
  exact mem_canonicalPositiveNegativeCrossPairs_iff.mpr
    ⟨hu, hq, Ne.symm hqu, hreverse⟩

/-- Swapping every strict nesting pair gives a subset of the oriented
canonical crossing relation. -/
noncomputable def swappedReducedCollisionStrictPositiveNestingPairs
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    Finset (ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h) := by
  classical
  exact (reducedCollisionStrictPositiveNestingPairs F).image
    (fun p ↦ (p.2, p.1))

/-- The swapped strict nesting family lies in the canonical crossing
relation. -/
theorem image_swap_strictPositiveNestingPairs_subset_crossPairs
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    swappedReducedCollisionStrictPositiveNestingPairs F ⊆
      canonicalPositiveNegativeCrossPairs (g := g) hh := by
  classical
  intro p hp
  rw [swappedReducedCollisionStrictPositiveNestingPairs] at hp
  rcases Finset.mem_image.mp hp with ⟨z, hz, rfl⟩
  have hz' := mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hz
  exact strictPositiveNesting_forces_reverse_canonicalCross
    hg hh hh0 z.1 z.2 (hcanonical hz'.1)
      (hcanonical hz'.2.1) hz'.2.2

/-- The complete strict-nesting face loss is charged injectively to the
face-weighted oriented canonical crossing relation. -/
theorem positiveUpperNestingFaceMass_le_canonicalCrossFaceMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    reducedCollisionPositiveUpperNestingFaceMass F ≤
      canonicalPositiveNegativeCrossFaceMass (g := g) hh := by
  classical
  let N := reducedCollisionStrictPositiveNestingPairs F
  let swap : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h →
      ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h :=
    fun p ↦ (p.2, p.1)
  let face : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    (reducedCollisionPositiveUpperValueLayer p.1).card
  have hinj : Set.InjOn swap ↑N := by
    intro p hp z hz heq
    exact Prod.ext (congrArg Prod.snd heq) (congrArg Prod.fst heq)
  have hsub : N.image swap ⊆
      canonicalPositiveNegativeCrossPairs (g := g) hh := by
    simpa [N, swap, swappedReducedCollisionStrictPositiveNestingPairs] using
      image_swap_strictPositiveNestingPairs_subset_crossPairs
        hg hh hh0 F hcanonical
  calc
    reducedCollisionPositiveUpperNestingFaceMass F =
        N.sum (fun p ↦ face (swap p)) := by
      rfl
    _ = (N.image swap).sum face := (Finset.sum_image hinj).symm
    _ ≤ (canonicalPositiveNegativeCrossPairs (g := g) hh).sum face :=
      Finset.sum_le_sum_of_subset hsub
    _ = canonicalPositiveNegativeCrossFaceMass (g := g) hh := rfl

/-- Diagonal part of the positive-upper duplication budget. -/
noncomputable def reducedCollisionPositiveUpperDiagonalCharge
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) : ℕ := by
  classical
  exact if q = u then
    (reducedCollisionPositiveUpperValueLayer q).card else 0

/-- One orientation of the strict positive-tail nesting charge. -/
noncomputable def reducedCollisionPositiveUpperStrictNestingCharge
    {g : Fin (m + 1) → G} {h : G}
    (q u : ReducedSubsetSumCollision g h) : ℕ := by
  classical
  exact if q.val.1 ⊂ u.val.1 then
    (reducedCollisionPositiveUpperValueLayer u).card else 0

/-- Pointwise decomposition of the duplication term into the diagonal and
the two possible strict-nesting orientations. -/
theorem positiveUpperPairDuplication_eq_diagonal_add_nesting
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (q u : ReducedSubsetSumCollision g h) :
    reducedCollisionPositiveUpperPairDuplication q u =
      reducedCollisionPositiveUpperDiagonalCharge q u +
        reducedCollisionPositiveUpperStrictNestingCharge q u +
        reducedCollisionPositiveUpperStrictNestingCharge u q := by
  classical
  by_cases hqu : q = u
  · subst u
    simp [reducedCollisionPositiveUpperPairDuplication,
      reducedCollisionPositiveUpperDiagonalCharge,
      reducedCollisionPositiveUpperStrictNestingCharge]
  by_cases hsub : q.val.1 ⊆ u.val.1
  · have hleft : q.val.1 ≠ u.val.1 := by
      intro hEq
      exact hqu (reducedSubsetSumCollision_eq_of_left_eq hg q u hEq)
    have hstrict : q.val.1 ⊂ u.val.1 :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hleft⟩
    have hnreverse : ¬u.val.1 ⊂ q.val.1 := by
      intro hr
      exact hr.2 hsub
    simp [reducedCollisionPositiveUpperPairDuplication,
      reducedCollisionPositiveUpperDiagonalCharge,
      reducedCollisionPositiveUpperStrictNestingCharge,
      hqu, hsub, hstrict, hnreverse]
  · by_cases husub : u.val.1 ⊆ q.val.1
    · have hleft : u.val.1 ≠ q.val.1 := by
        intro hEq
        apply hsub
        rw [hEq]
      have hstrict : u.val.1 ⊂ q.val.1 :=
        Finset.ssubset_iff_subset_ne.mpr ⟨husub, hleft⟩
      have hnforward : ¬q.val.1 ⊂ u.val.1 := by
        intro hf
        exact hsub hf.1
      simp [reducedCollisionPositiveUpperPairDuplication,
        reducedCollisionPositiveUpperDiagonalCharge,
        reducedCollisionPositiveUpperStrictNestingCharge,
        hqu, hsub, husub, hstrict, hnforward]
    · have hnforward : ¬q.val.1 ⊂ u.val.1 := fun hf ↦ hsub hf.1
      have hnreverse : ¬u.val.1 ⊂ q.val.1 := fun hr ↦ husub hr.1
      simp [reducedCollisionPositiveUpperPairDuplication,
        reducedCollisionPositiveUpperDiagonalCharge,
        reducedCollisionPositiveUpperStrictNestingCharge,
        hqu, hsub, husub, hnforward, hnreverse]

/-- Exact all-family decomposition of the previous milestone's pair budget.
The two ordered copies of each strict containment explain the factor two. -/
theorem positiveUpperPairBudget_eq_card_succ_mul_incidence_add_two_mul_nesting
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionPositiveUpperPairBudget F =
      (F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
        2 * reducedCollisionPositiveUpperNestingFaceMass F := by
  classical
  rw [reducedCollisionPositiveUpperPairBudget]
  have hdup :
      (F ×ˢ F).sum (fun p ↦
          reducedCollisionPositiveUpperPairDuplication p.1 p.2) =
        reducedCollisionPositiveUpperIncidenceMass F +
          2 * reducedCollisionPositiveUpperNestingFaceMass F := by
    have hpointwise :
        (F ×ˢ F).sum (fun p ↦
            reducedCollisionPositiveUpperPairDuplication p.1 p.2) =
          (F ×ˢ F).sum (fun p ↦
            (reducedCollisionPositiveUpperDiagonalCharge p.1 p.2 +
              reducedCollisionPositiveUpperStrictNestingCharge p.1 p.2) +
              reducedCollisionPositiveUpperStrictNestingCharge p.2 p.1) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [positiveUpperPairDuplication_eq_diagonal_add_nesting hg p.1 p.2]
    have hdiag :
        (F ×ˢ F).sum (fun p ↦
            reducedCollisionPositiveUpperDiagonalCharge p.1 p.2) =
          reducedCollisionPositiveUpperIncidenceMass F := by
      rw [Finset.sum_product]
      simp [reducedCollisionPositiveUpperDiagonalCharge,
        reducedCollisionPositiveUpperIncidenceMass,
        reducedCollisionPositiveUpperValueLayer]
    have hnest :
        (F ×ˢ F).sum (fun p ↦
            reducedCollisionPositiveUpperStrictNestingCharge p.1 p.2) =
          reducedCollisionPositiveUpperNestingFaceMass F := by
      simp [reducedCollisionPositiveUpperStrictNestingCharge,
        reducedCollisionPositiveUpperNestingFaceMass,
        reducedCollisionStrictPositiveNestingPairs, Finset.sum_filter]
    have hreverse :
        (F ×ˢ F).sum (fun p ↦
            reducedCollisionPositiveUpperStrictNestingCharge p.2 p.1) =
          reducedCollisionPositiveUpperNestingFaceMass F := by
      rw [Finset.sum_product, Finset.sum_comm]
      rw [Finset.sum_product] at hnest
      simpa only [Prod.fst, Prod.snd] using hnest
    rw [hpointwise, Finset.sum_add_distrib, Finset.sum_add_distrib,
      hdiag, hnest, hreverse]
    omega
  rw [Finset.sum_add_distrib, hdup]
  have hbase :
      (F ×ˢ F).sum (fun p ↦
          (reducedCollisionPositiveUpperValueLayer p.1).card) =
        F.card * reducedCollisionPositiveUpperIncidenceMass F := by
    rw [Finset.sum_product]
    simp only [Finset.sum_const, nsmul_eq_mul]
    rw [reducedCollisionPositiveUpperIncidenceMass, Finset.mul_sum]
    rfl
  rw [hbase]
  ring

/-- All strict-nesting loss in `PairBudget` is bounded by the canonical
crossing face mass. -/
theorem positiveUpperPairBudget_le_card_succ_mul_incidence_add_two_mul_crossFaceMass
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    reducedCollisionPositiveUpperPairBudget F ≤
      (F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
        2 * canonicalPositiveNegativeCrossFaceMass (g := g) hh := by
  rw [positiveUpperPairBudget_eq_card_succ_mul_incidence_add_two_mul_nesting
    hg F]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul_left 2
      (positiveUpperNestingFaceMass_le_canonicalCrossFaceMass
        hg hh hh0 F hcanonical)) _

/-- The all-family upper-face second moment after charging strict nesting to
canonical crossings. -/
theorem two_mul_positiveUpperIncidenceMass_sq_le_union_mul_card_succ_incidence_add_cross
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonical : F ⊆ canonicalReducedCollisions (g := g) hh) :
    2 * (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll F).card *
        ((F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
          2 * canonicalPositiveNegativeCrossFaceMass (g := g) hh) := by
  exact (two_mul_positiveUpperIncidenceMass_sq_le_union_mul_pairBudget hg F).trans
    (Nat.mul_le_mul_left _
      (positiveUpperPairBudget_le_card_succ_mul_incidence_add_two_mul_crossFaceMass
        hg hh hh0 F hcanonical))

/-- Factor-eight large-support supply combined with the nesting-to-crossing
charge. -/
theorem oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_card_succ_incidence_add_cross
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonicalMem : F ⊆ canonicalReducedCollisions (g := g) hh)
    (hcanonicalCard : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    128 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll F).card *
        ((F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
          2 * canonicalPositiveNegativeCrossFaceMass (g := g) hh) := by
  have hmass := eight_mul_sum_weight_le_positiveUpperIncidenceMass
    hg F hcanonicalCard hsix
  have hsq' := Nat.mul_le_mul hmass hmass
  have hsq : (8 * F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
      (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 := by
    simpa [pow_two] using hsq'
  have hsecond :=
    two_mul_positiveUpperIncidenceMass_sq_le_union_mul_card_succ_incidence_add_cross
      hg hh hh0 F hcanonicalMem
  calc
    128 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 =
        2 * (8 * F.sum (reducedCollisionWeight (m := m))) ^ 2 := by ring
    _ ≤ 2 * (reducedCollisionPositiveUpperIncidenceMass F) ^ 2 :=
      Nat.mul_le_mul_left 2 hsq
    _ ≤ (reducedCollisionPositiveUpperValueUnionAll F).card *
        ((F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
          2 * canonicalPositiveNegativeCrossFaceMass (g := g) hh) := hsecond

section CriticalNestingCharge

/-- Milestone 2cv: in the genuine live-root residual, all strict positive-tail
nesting is charged to the face-weighted oriented canonical crossing relation.
The remaining quantitative task is to compare that face mass with the already
small product-weight crossing mass (or absorb it into the restoration union). -/
theorem genuineDominant_liveRoot_largeSupport_positiveUpper_nestingCharged
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
      rw [pow_succ]
      ring
    let hh := half_add_half hN
    let F := criticalCanonicalNonrootCollisions g r
    reducedCollisionPositiveUpperNestingFaceMass F ≤
        canonicalPositiveNegativeCrossFaceMass (g := g) hh ∧
      reducedCollisionPositiveUpperPairBudget F =
        (F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
          2 * reducedCollisionPositiveUpperNestingFaceMass F ∧
      128 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll F).card *
          ((F.card + 1) * reducedCollisionPositiveUpperIncidenceMass F +
            2 * canonicalPositiveNegativeCrossFaceMass (g := g) hh) ∧
      (reducedCollisionPositiveUpperValueUnionAll F).card ≤ 2 ^ n := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  let hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
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
  have hcanonicalMem : F ⊆ canonicalReducedCollisions (g := g) hh := by
    intro v hv
    simpa [hh, criticalCanonicalReducedCollisions] using (hmem v hv).1
  have hcanonicalCard : ∀ v ∈ F, v.val.1.card ≤ v.val.2.card := by
    intro v hv
    exact canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp (hcanonicalMem hv))
  have hsix : ∀ v ∈ F, 6 ≤ (reducedCollisionSupport v).card := by
    intro v hv
    exact genuineDominant_liveRoot_all_other_support_card_six_le
      hqodd g hg r hr hres hAcard hBcard v
        (hmem v hv).1 (hmem v hv).2
  refine ⟨
    positiveUpperNestingFaceMass_le_canonicalCrossFaceMass
      hg hh (half_ne_zero hN
        (mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s)
          (Odd.pos hqodd))) F hcanonicalMem,
    positiveUpperPairBudget_eq_card_succ_mul_incidence_add_two_mul_nesting
      hg F,
    oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_card_succ_incidence_add_cross
      hg hh (half_ne_zero hN
        (mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s)
          (Odd.pos hqodd))) F hcanonicalMem hcanonicalCard hsix,
    ?_⟩
  calc
    (reducedCollisionPositiveUpperValueUnionAll F).card ≤
        (subsetSumRange g).card := Finset.card_le_card
          (reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange F)
    _ = 2 ^ n := card_subsetSumRange g hg

end CriticalNestingCharge

end MinModulus
