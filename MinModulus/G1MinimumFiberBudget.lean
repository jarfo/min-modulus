/-
# Minimum-fiber signatures and their grouped target-weight budget

The exact slice mass is strongest when the signature selected at a covered
coordinate has minimum escape-fiber cardinality.  `selectedCoveringSignature`
now makes this choice.  This file supplies the complementary global fact:
after quotienting targets by blocked signature, choose one realizing target
per signature.  Distinct signatures give distinct targets, so strict majority
charges their weights only once.  The target fiber estimate then yields

`2 * sum_C |B_r \ C| < w_r`.

The selected signatures still cover the whole negative tail, inherit this
same grouped budget, and retain the minimum-fiber property coordinatewise.
Together with the fiber-adaptive Boolean-cube inequality, this is a finite
parameter optimization interface for the genuine dominant G1 residual.
-/
import MinModulus.G1FiberAdaptiveSlices

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- One actual escape target realizing a blocked signature, with the root as
an irrelevant fallback outside the realized-signature family. -/
noncomputable def realizingEscapeTargetForSignature
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) (C : Finset (Fin m)) :
    ReducedSubsetSumCollision g h := by
  classical
  exact if hC : C ∈ canonicalSupportEscapeBlockedSignatures hh r then
    Classical.choose
      (mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC)
  else r

theorem realizingEscapeTargetForSignature_mem_and_blockedSupport
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) {C : Finset (Fin m)}
    (hC : C ∈ canonicalSupportEscapeBlockedSignatures hh r) :
    realizingEscapeTargetForSignature hh r C ∈
        canonicalSupportEscapeTargets hh r ∧
      restoredCollisionBlockedSupport r
        (realizingEscapeTargetForSignature hh r C) = C := by
  classical
  rw [realizingEscapeTargetForSignature, dif_pos hC]
  exact Classical.choose_spec
    (mem_canonicalSupportEscapeBlockedSignatures_iff.mp hC)

/-- Choosing one target per signature is injective on realized signatures. -/
theorem realizingEscapeTargetForSignature_injOn
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    Set.InjOn (realizingEscapeTargetForSignature hh r)
      (canonicalSupportEscapeBlockedSignatures hh r :
        Set (Finset (Fin m))) := by
  classical
  intro C hC D hD hCD
  have hCspec := realizingEscapeTargetForSignature_mem_and_blockedSupport
    hh r hC
  have hDspec := realizingEscapeTargetForSignature_mem_and_blockedSupport
    hh r hD
  calc
    C = restoredCollisionBlockedSupport r
        (realizingEscapeTargetForSignature hh r C) := hCspec.2.symm
    _ = restoredCollisionBlockedSupport r
        (realizingEscapeTargetForSignature hh r D) := by rw [hCD]
    _ = D := hDspec.2

/-- The total weights of one representative per distinct escape signature
fit strictly below the dominant root weight. -/
theorem sum_realizingEscapeTargetWeights_lt_rootWeight
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    (canonicalSupportEscapeBlockedSignatures hh r).sum (fun C ↦
        reducedCollisionWeight (m := m)
          (realizingEscapeTargetForSignature hh r C)) <
      reducedCollisionWeight (m := m) r := by
  classical
  let S := canonicalSupportEscapeBlockedSignatures hh r
  let f := realizingEscapeTargetForSignature hh r
  let collisions := canonicalReducedCollisions (g := g) hh
  have himageSubset : S.image f ⊆ collisions.erase r := by
    intro u hu
    rcases Finset.mem_image.mp hu with ⟨D, hDS, rfl⟩
    have htarget :=
      (realizingEscapeTargetForSignature_mem_and_blockedSupport
        hh r hDS).1
    rcases mem_canonicalSupportEscapeTargets_iff.mp htarget with ⟨j, hj⟩
    have hj' := mem_canonicalSupportEscapeIncidences_iff.mp hj
    have hne : realizingEscapeTargetForSignature hh r D ≠ r := by
      intro heq
      rw [heq] at hj'
      exact hj'.2.2.1 (Finset.mem_union_right _ hj'.1)
    exact Finset.mem_erase.mpr ⟨hne, hj'.2.1⟩
  have himageLe : (S.image f).sum (reducedCollisionWeight (m := m)) ≤
      (collisions.erase r).sum (reducedCollisionWeight (m := m)) :=
    Finset.sum_le_sum_of_subset himageSubset
  have herase : (collisions.erase r).sum
        (reducedCollisionWeight (m := m)) +
      reducedCollisionWeight (m := m) r =
        collisions.sum (reducedCollisionWeight (m := m)) :=
    Finset.sum_erase_add collisions (reducedCollisionWeight (m := m)) hr
  have heraseLt : (collisions.erase r).sum
      (reducedCollisionWeight (m := m)) <
        reducedCollisionWeight (m := m) r := by
    have hmajor' : collisions.sum (reducedCollisionWeight (m := m)) <
        2 * reducedCollisionWeight (m := m) r := by
      simpa [collisions] using hmajor
    omega
  calc
    S.sum (fun D ↦ reducedCollisionWeight (m := m) (f D)) =
        (S.image f).sum (reducedCollisionWeight (m := m)) := by
      symm
      exact Finset.sum_image
        (realizingEscapeTargetForSignature_injOn hh r)
    _ ≤ (collisions.erase r).sum
        (reducedCollisionWeight (m := m)) := himageLe
    _ < reducedCollisionWeight (m := m) r := heraseLt

/-- The sum of the cardinalities of all distinct realized signature fibers. -/
noncomputable def escapeBlockedSignatureFiberCardSum
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : ℕ :=
  (canonicalSupportEscapeBlockedSignatures hh r).sum
    (fun C ↦ (blockedSignatureEscapeFiber r C).card)

/-- Distinct signatures pay their fiber-cardinality tax from distinct target
weights.  This is the grouped form of the pointwise target-fiber estimate. -/
theorem two_mul_escapeBlockedSignatureFiberCardSum_lt_rootWeight
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    2 * escapeBlockedSignatureFiberCardSum hh r <
      reducedCollisionWeight (m := m) r := by
  classical
  let S := canonicalSupportEscapeBlockedSignatures hh r
  let f := realizingEscapeTargetForSignature hh r
  have hpointwise : ∀ C ∈ S,
      2 * (blockedSignatureEscapeFiber r C).card ≤
        reducedCollisionWeight (m := m) (f C) := by
    intro C hCS
    have hspec := realizingEscapeTargetForSignature_mem_and_blockedSupport
      hh r hCS
    rcases mem_canonicalSupportEscapeTargets_iff.mp hspec.1 with ⟨j, hj⟩
    have hj' := mem_canonicalSupportEscapeIncidences_iff.mp hj
    have htarget := two_mul_escapeFiberCard_le_targetWeight
      hh r (f C) hrmin hspec.1
    have hfiber :=
      canonicalSupportEscapeTargetFiber_eq_sourceTail_sdiff_blockedSupport
        r (f C) (hrmin (f C) hj'.2.1) hj'.2.2.2
    rw [hfiber, hspec.2] at htarget
    exact htarget
  have hsum : S.sum (fun C ↦
      2 * (blockedSignatureEscapeFiber r C).card) ≤
      S.sum (fun C ↦ reducedCollisionWeight (m := m) (f C)) :=
    Finset.sum_le_sum hpointwise
  have hweight := sum_realizingEscapeTargetWeights_lt_rootWeight
    hh r hr hmajor
  change 2 * S.sum (fun C ↦
      (blockedSignatureEscapeFiber r C).card) <
    reducedCollisionWeight (m := m) r
  rw [Finset.mul_sum]
  exact hsum.trans_lt (by simpa [S, f] using hweight)

/-- The distinct signatures actually selected by the minimum-fiber rule on
a coordinate set. -/
noncomputable def selectedCoveringSignatures
    (S : Finset (Finset (Fin m))) (B Q : Finset (Fin m)) :
    Finset (Finset (Fin m)) := by
  classical
  exact Q.image (selectedCoveringSignature S B)

/-- Number of coordinates assigned to one selected minimum-fiber signature. -/
noncomputable def selectedCoveringSignatureMultiplicity
    (S : Finset (Finset (Fin m))) (B Q : Finset (Fin m))
    (C : Finset (Fin m)) : ℕ := by
  classical
  exact (Q.filter (fun j ↦ selectedCoveringSignature S B j = C)).card

/-- The coordinatewise slice mass regroups exactly by distinct selected
signatures and their multiplicities. -/
theorem selectedFiberSliceMass_eq_sum_selectedSignatureMultiplicities
    (S : Finset (Finset (Fin m))) (B Q : Finset (Fin m)) :
    selectedFiberSliceMass S B Q =
      (selectedCoveringSignatures S B Q).sum (fun C ↦
        selectedCoveringSignatureMultiplicity S B Q C *
          2 ^ (m - (C ∪ B).card)) := by
  classical
  have hcomp := Finset.sum_comp
    (s := Q)
    (fun C : Finset (Fin m) ↦ 2 ^ (m - (C ∪ B).card))
    (selectedCoveringSignature S B)
  simp only [Nat.nsmul_eq_mul] at hcomp
  simpa [selectedFiberSliceMass, selectedCoveringSignatures,
    selectedCoveringSignatureMultiplicity] using hcomp

/-- When all realized signatures have the root cardinality, the grouped mass
has the pure parameter form `sum_C t_C * 2^(padding-|B\C|)`. -/
theorem selectedFiberSliceMass_eq_sum_multiplicity_mul_pow_padding_sub_fiberCard
    (R B : Finset (Fin m)) (S : Finset (Finset (Fin m)))
    (hcards : ∀ C ∈ S, C.card = R.card)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    selectedFiberSliceMass S B B =
      (selectedCoveringSignatures S B B).sum (fun C ↦
        selectedCoveringSignatureMultiplicity S B B C *
          2 ^ (m - R.card - (B \ C).card)) := by
  classical
  rw [selectedFiberSliceMass_eq_sum_selectedSignatureMultiplicities]
  apply Finset.sum_congr rfl
  intro C hC
  have hCS : C ∈ S := by
    rcases Finset.mem_image.mp hC with ⟨j, hjB, rfl⟩
    exact (selectedCoveringSignature_mem_and_covers_of_biUnion_eq
      S B hcover hjB).1
  have hunion : (C ∪ B).card = C.card + (B \ C).card := by
    have hinterle : (B ∩ C).card ≤ B.card :=
      Finset.card_le_card Finset.inter_subset_left
    rw [Finset.card_union, Finset.card_sdiff]
    rw [Finset.inter_comm C B]
    omega
  rw [hunion, hcards C hCS]
  congr 2
  omega

/-- Selected multiplicities partition the coordinate set. -/
theorem sum_selectedCoveringSignatureMultiplicities
    (S : Finset (Finset (Fin m))) (B Q : Finset (Fin m)) :
    (selectedCoveringSignatures S B Q).sum
        (selectedCoveringSignatureMultiplicity S B Q) = Q.card := by
  classical
  have h := Finset.sum_comp
    (s := Q) (fun _ : Finset (Fin m) ↦ (1 : ℕ))
    (selectedCoveringSignature S B)
  simpa [selectedCoveringSignatures,
    selectedCoveringSignatureMultiplicity] using h.symm

theorem selectedCoveringSignatures_subset
    (S : Finset (Finset (Fin m))) (B Q : Finset (Fin m))
    (hQB : Q ⊆ B)
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    selectedCoveringSignatures S B Q ⊆ S := by
  classical
  intro C hC
  rcases Finset.mem_image.mp hC with ⟨j, hjQ, rfl⟩
  exact (selectedCoveringSignature_mem_and_covers_of_biUnion_eq
    S B hcover (hQB hjQ)).1

/-- Every selected signature receives at least one coordinate. -/
theorem selectedCoveringSignatureMultiplicity_pos
    (S : Finset (Finset (Fin m))) (B Q : Finset (Fin m))
    {C : Finset (Fin m)} (hC : C ∈ selectedCoveringSignatures S B Q) :
    0 < selectedCoveringSignatureMultiplicity S B Q C := by
  classical
  rcases Finset.mem_image.mp hC with ⟨j, hjQ, hjC⟩
  rw [selectedCoveringSignatureMultiplicity, Finset.card_pos]
  exact ⟨j, Finset.mem_filter.mpr ⟨hjQ, hjC⟩⟩

/-- Coordinates assigned to a selected signature lie in that signature's
escape fiber, so its multiplicity never exceeds its fiber cardinality. -/
theorem selectedCoveringSignatureMultiplicity_le_fiberCard
    (S : Finset (Finset (Fin m))) (B Q : Finset (Fin m))
    (hQB : Q ⊆ B)
    (hcover : S.biUnion (fun C ↦ B \ C) = B)
    (C : Finset (Fin m)) :
    selectedCoveringSignatureMultiplicity S B Q C ≤ (B \ C).card := by
  classical
  apply Finset.card_le_card
  intro j hj
  have hj' := Finset.mem_filter.mp hj
  have hjB := hQB hj'.1
  have hjCover :=
    (selectedCoveringSignature_mem_and_covers_of_biUnion_eq
      S B hcover hjB).2
  exact Finset.mem_sdiff.mpr ⟨hjB, by
    intro hjCmem
    have : j ∉ selectedCoveringSignature S B j :=
      (Finset.mem_sdiff.mp hjCover).2
    exact this (by simpa [hj'.2] using hjCmem)⟩

/-- For the whole tail, the selected minimum fibers still cover every
coordinate exactly as a union (overlaps are allowed). -/
theorem selectedCoveringSignatureCoverage_eq
    (S : Finset (Finset (Fin m))) (B : Finset (Fin m))
    (hcover : S.biUnion (fun C ↦ B \ C) = B) :
    (selectedCoveringSignatures S B B).biUnion (fun C ↦ B \ C) = B := by
  classical
  apply Finset.Subset.antisymm
  · intro j hj
    rcases Finset.mem_biUnion.mp hj with ⟨C, _, hjC⟩
    exact (Finset.mem_sdiff.mp hjC).1
  · intro j hjB
    have hj := selectedCoveringSignature_mem_and_covers_of_biUnion_eq
      S B hcover hjB
    exact Finset.mem_biUnion.mpr
      ⟨selectedCoveringSignature S B j,
        Finset.mem_image.mpr ⟨j, hjB, rfl⟩, hj.2⟩

/-- The selected distinct minimum fibers inherit the global grouped budget. -/
theorem two_mul_selectedCoveringSignatureFiberSum_lt_rootWeight
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    let S := canonicalSupportEscapeBlockedSignatures hh r
    2 * (selectedCoveringSignatures S r.val.2 r.val.2).sum
        (fun C ↦ (blockedSignatureEscapeFiber r C).card) <
      reducedCollisionWeight (m := m) r := by
  classical
  dsimp only
  let S := canonicalSupportEscapeBlockedSignatures hh r
  let T := selectedCoveringSignatures S r.val.2 r.val.2
  have hcover' : S.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 := by
    change canonicalSupportEscapeBlockedSignatureCoverage hh r = r.val.2
    exact hcover
  have hTsub : T ⊆ S :=
    selectedCoveringSignatures_subset S r.val.2 r.val.2
      (by rfl) hcover'
  have hsumLe : T.sum (fun C ↦
      (blockedSignatureEscapeFiber r C).card) ≤
      S.sum (fun C ↦ (blockedSignatureEscapeFiber r C).card) :=
    Finset.sum_le_sum_of_subset hTsub
  have hall := two_mul_escapeBlockedSignatureFiberCardSum_lt_rootWeight
    hh r hr hrmin hmajor
  change 2 * T.sum (fun C ↦
      (blockedSignatureEscapeFiber r C).card) <
    reducedCollisionWeight (m := m) r
  exact (Nat.mul_le_mul_left 2 hsumLe).trans_lt (by
    simpa [escapeBlockedSignatureFiberCardSum, S] using hall)

/-- Abstract collision package: minimum fiber choice at every tail coordinate,
coverage by the distinct selected signatures, the grouped fiber-cardinality
budget, and the exact fiber-adaptive Boolean-cube constraint all hold
simultaneously. -/
theorem minimumFiber_groupedBudget_and_tailFace_bound
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hrmin : ∀ q ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport q).card)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    (hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2) :
    let S := canonicalSupportEscapeBlockedSignatures hh r
    let T := selectedCoveringSignatures S r.val.2 r.val.2
    (∀ j ∈ r.val.2, ∀ C ∈ S, j ∈ r.val.2 \ C →
      (r.val.2 \ selectedCoveringSignature S r.val.2 j).card ≤
        (r.val.2 \ C).card) ∧
    T.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 ∧
    2 * T.sum (fun C ↦ (blockedSignatureEscapeFiber r C).card) <
      reducedCollisionWeight (m := m) r ∧
    max (2 * reducedCollisionWeight (m := m) r)
        (reducedCollisionWeight (m := m) r +
          selectedFiberSliceMass S r.val.2 r.val.2) +
      2 ^ (m - r.val.2.card) ≤ 2 ^ m := by
  classical
  dsimp only
  let S := canonicalSupportEscapeBlockedSignatures hh r
  let T := selectedCoveringSignatures S r.val.2 r.val.2
  have hcover' : S.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 := by
    change canonicalSupportEscapeBlockedSignatureCoverage hh r = r.val.2
    exact hcover
  have hminimum : ∀ j ∈ r.val.2, ∀ C ∈ S,
      j ∈ r.val.2 \ C →
        (r.val.2 \ selectedCoveringSignature S r.val.2 j).card ≤
          (r.val.2 \ C).card := by
    intro j hjB C hCS hjC
    exact selectedCoveringSignature_fiberCard_le S r.val.2 j
      (by
        have hjUnion : j ∈ S.biUnion (fun D ↦ r.val.2 \ D) := by
          rw [hcover']
          exact hjB
        rcases Finset.mem_biUnion.mp hjUnion with ⟨D, hDS, hjD⟩
        exact ⟨D, hDS, hjD⟩)
      hCS hjC
  have hselectedCover := selectedCoveringSignatureCoverage_eq
    S r.val.2 hcover'
  have hbudget :=
    two_mul_selectedCoveringSignatureFiberSum_lt_rootWeight
      hh r hr hrmin hmajor hcover
  have hcube :=
    max_twoWeight_rootAddSelectedFiberMass_add_negativeTailFace_le_fullCube
      hg hh hh0 r hr hrmin hcover
  exact ⟨hminimum, hselectedCover, hbudget, hcube⟩

/-- The strengthened one-root parameter package is still not contradictory by
itself.  With padding `d+3`, two selected singleton fibers have total fiber
tax `4 < 2^(d+3)`, adaptive mass exactly the root weight, and satisfy the
resulting cube inequality for the symbolic profile `(|A|,|B|)=(1,2)`.
Consequently the next G1 count must couple the two selected target roots. -/
theorem two_singleton_minimumFiber_profile_remains_feasible (d : ℕ) :
    let w := 2 ^ (d + 3)
    let M := 2 ^ (d + 2) + 2 ^ (d + 2)
    2 * (1 + 1) < w ∧
      M = w ∧
      max (2 * w) (w + M) + 2 ^ (d + 4) ≤ 2 ^ (d + 6) := by
  dsimp only
  have hpos : 0 < 2 ^ d := by positivity
  simp only [pow_add]
  norm_num
  omega

section CriticalMinimumFiberBudget

/-- In every genuine critical dominant G1 residual, the minimum-fiber
selection, grouped target-weight tax, exact coverage, and fiber-adaptive cube
bound survive as one parameter-only obstruction package. -/
theorem genuineDominant_minimumFiber_groupedBudget_and_tailFace_bound
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
    let T := selectedCoveringSignatures S r.val.2 r.val.2
    (∀ j ∈ r.val.2, ∀ C ∈ S, j ∈ r.val.2 \ C →
      (r.val.2 \ selectedCoveringSignature S r.val.2 j).card ≤
        (r.val.2 \ C).card) ∧
    T.biUnion (fun C ↦ r.val.2 \ C) = r.val.2 ∧
    2 * T.sum (fun C ↦ (blockedSignatureEscapeFiber r C).card) <
      reducedCollisionWeight (m := n) r ∧
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
  have hmajor : (canonicalReducedCollisions (g := g) hh).sum
      (reducedCollisionWeight (m := n)) <
        2 * reducedCollisionWeight (m := n) r := by
    simpa [hh, criticalCanonicalReducedCollisions] using hdominant.2.2.1
  have hcover : canonicalSupportEscapeBlockedSignatureCoverage hh r =
      r.val.2 := by
    simpa [hh] using hdominant.2.2.2.2.2.2.2.2.2.1
  simpa [hh] using minimumFiber_groupedBudget_and_tailFace_bound
    hg hh (half_ne_zero hN hM) r hr' hrmin hmajor hcover

end CriticalMinimumFiberBudget

end MinModulus
