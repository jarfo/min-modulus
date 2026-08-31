/-
# Dense positive/negative crossings in the canonical family

The heavy-or-cross trichotomy leaves a crossing branch.  In fact validity
forces such crossings pairwise throughout the canonical family.  Subtracting
the collision witnesses of two distinct shapes gives a nonzero zero-target
relation.  Unless the old negative tail meets the new positive tail, its only
possible floor failure is at the anchor, where the new imbalance must exceed
the old one by at least two.  Applying this statement in both directions
rules out simultaneous anchor gaps.

Thus every unordered pair of distinct canonical collisions has a
positive-to-negative crossing in at least one orientation.  The finite
oriented crossing relation consequently contains at least half of all ordered
distinct pairs.  This replaces the single crossing from the trichotomy by a
dense family available for weighted counting.
-/
import MinModulus.G1HeavyOrCross

namespace MinModulus

open Finset

variable {m : ℕ}

/-- Equality of coefficient vectors for disjoint collision pairs recovers
both sides exactly. -/
theorem subsetCollisionCoeffs_eq_of_disjoint_imp_eq
    {A₁ B₁ A₂ B₂ : Finset (Fin m)}
    (hd₁ : Disjoint A₁ B₁) (hd₂ : Disjoint A₂ B₂)
    (hcoeff : subsetCollisionCoeffs A₁ B₁ =
      subsetCollisionCoeffs A₂ B₂) :
    A₁ = A₂ ∧ B₁ = B₂ := by
  have hd₁' := Finset.disjoint_left.mp hd₁
  have hd₂' := Finset.disjoint_left.mp hd₂
  constructor <;> ext j
  · have hv := congrFun hcoeff j.succ
    simp only [subsetCollisionCoeffs, Fin.cons_succ] at hv
    by_cases hA₁ : j ∈ A₁ <;> by_cases hB₁ : j ∈ B₁ <;>
      by_cases hA₂ : j ∈ A₂ <;> by_cases hB₂ : j ∈ B₂ <;>
      simp_all
  · have hv := congrFun hcoeff j.succ
    simp only [subsetCollisionCoeffs, Fin.cons_succ] at hv
    by_cases hA₁ : j ∈ A₁ <;> by_cases hB₁ : j ∈ B₁ <;>
      by_cases hA₂ : j ∈ A₂ <;> by_cases hB₂ : j ∈ B₂ <;>
      simp_all

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- For two distinct cardinality-oriented reduced collisions, validity forces
either a reverse negative/positive crossing or an imbalance increase of at
least two. -/
theorem reducedCollision_reverse_cross_or_imbalance_gap
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hrcard : r.val.1.card ≤ r.val.2.card)
    (hqcard : q.val.1.card ≤ q.val.2.card)
    (hqr : q ≠ r) :
    (r.val.2 ∩ q.val.1).Nonempty ∨
      reducedCollisionImbalance r + 2 ≤ reducedCollisionImbalance q := by
  by_contra hbad
  rw [not_or] at hbad
  have hnoCross : ∀ k : Fin m, k ∈ r.val.2 → k ∈ q.val.1 → False := by
    intro k hkr hkq
    exact hbad.1 ⟨k, Finset.mem_inter.mpr ⟨hkr, hkq⟩⟩
  have hrw := witness_of_subsetSum_eq_add g hh0 hrcard r.property.2
  have hqw := witness_of_subsetSum_eq_add g hh0 hqcard q.property.2
  apply (validTuple_iff_no_zero_witness g).mp hg
    (subsetCollisionCoeffs r.val.1 r.val.2 -
      subsetCollisionCoeffs q.val.1 q.val.2)
  apply witness_sub_at_zero_of_floor g hrw hqw
  · intro hzero
    have hcoeff : subsetCollisionCoeffs r.val.1 r.val.2 =
        subsetCollisionCoeffs q.val.1 q.val.2 := by
      funext i
      have hi := congrFun hzero i
      simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at hi
      exact hi
    have hpairs := subsetCollisionCoeffs_eq_of_disjoint_imp_eq
      r.property.1 q.property.1 hcoeff
    apply hqr
    apply Subtype.ext
    apply Prod.ext
    · exact hpairs.1.symm
    · exact hpairs.2.symm
  · intro i
    refine Fin.cases ?_ ?_ i
    · have hrz := reducedCollisionImbalance_cast r hrcard
      have hqz := reducedCollisionImbalance_cast q hqcard
      simp only [Pi.sub_apply, subsetCollisionCoeffs, Fin.cons_zero]
      omega
    · intro k
      have hdr := Finset.disjoint_left.mp r.property.1
      have hdq := Finset.disjoint_left.mp q.property.1
      simp only [Pi.sub_apply]
      by_cases hrA : k ∈ r.val.1 <;> by_cases hrB : k ∈ r.val.2 <;>
        by_cases hqA : k ∈ q.val.1 <;> by_cases hqB : k ∈ q.val.2 <;>
        simp_all [subsetCollisionCoeffs]

/-- Every distinct pair of canonical collisions has a positive-to-negative
tail crossing in at least one of its two orientations. -/
theorem distinct_canonicalReducedCollisions_positive_negative_cross
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hr : IsCanonicalReducedCollision hh r)
    (hq : IsCanonicalReducedCollision hh q)
    (hqr : q ≠ r) :
    (r.val.1 ∩ q.val.2).Nonempty ∨
      (q.val.1 ∩ r.val.2).Nonempty := by
  rcases reducedCollision_reverse_cross_or_imbalance_gap
      g hg hh0 r q (canonicalReducedCollision_card_le hr)
        (canonicalReducedCollision_card_le hq) hqr with hreverse | hgap
  · exact Or.inr (by simpa [Finset.inter_comm] using hreverse)
  · rcases reducedCollision_reverse_cross_or_imbalance_gap
        g hg hh0 q r (canonicalReducedCollision_card_le hq)
          (canonicalReducedCollision_card_le hr) (Ne.symm hqr) with
      hforward | hgap'
    · exact Or.inl (by simpa [Finset.inter_comm] using hforward)
    · omega

/-- Ordered pairs of distinct canonical reduced collisions. -/
noncomputable def canonicalDistinctReducedCollisionPairs
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) :
    Finset (ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h) := by
  classical
  exact ((canonicalReducedCollisions (g := g) hh) ×ˢ
    (canonicalReducedCollisions (g := g) hh)).filter (fun p ↦ p.1 ≠ p.2)

/-- Ordered canonical pairs whose source positive tail meets the target
negative tail. -/
noncomputable def canonicalPositiveNegativeCrossPairs
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) :
    Finset (ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h) := by
  classical
  exact ((canonicalReducedCollisions (g := g) hh) ×ˢ
    (canonicalReducedCollisions (g := g) hh)).filter (fun p ↦
      p.1 ≠ p.2 ∧ (p.1.val.1 ∩ p.2.val.2).Nonempty)

@[simp] theorem mem_canonicalDistinctReducedCollisionPairs_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r q : ReducedSubsetSumCollision g h} :
    (r, q) ∈ canonicalDistinctReducedCollisionPairs hh ↔
      r ∈ canonicalReducedCollisions (g := g) hh ∧
        q ∈ canonicalReducedCollisions (g := g) hh ∧ r ≠ q := by
  classical
  simp [canonicalDistinctReducedCollisionPairs, and_assoc]

@[simp] theorem mem_canonicalPositiveNegativeCrossPairs_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r q : ReducedSubsetSumCollision g h} :
    (r, q) ∈ canonicalPositiveNegativeCrossPairs hh ↔
      r ∈ canonicalReducedCollisions (g := g) hh ∧
        q ∈ canonicalReducedCollisions (g := g) hh ∧ r ≠ q ∧
          (r.val.1 ∩ q.val.2).Nonempty := by
  classical
  simp [canonicalPositiveNegativeCrossPairs, and_assoc]

/-- Reversal of the oriented crossing relation. -/
noncomputable def reversedCanonicalPositiveNegativeCrossPairs
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) :
    Finset (ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h) := by
  classical
  exact (canonicalPositiveNegativeCrossPairs (g := g) hh).image
    (fun p ↦ (p.2, p.1))

/-- Every ordered distinct pair is either an oriented crossing or the reverse
of one.  The pointwise form avoids choosing decidable equality in the theorem
signature. -/
theorem mem_cross_or_reverse_of_mem_canonicalDistinctPairs
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    {p : ReducedSubsetSumCollision g h × ReducedSubsetSumCollision g h}
    (hp : p ∈ canonicalDistinctReducedCollisionPairs (g := g) hh) :
    p ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∨
      p ∈ reversedCanonicalPositiveNegativeCrossPairs (g := g) hh := by
  classical
  have hp' := (mem_canonicalDistinctReducedCollisionPairs_iff).mp hp
  have hrc := mem_canonicalReducedCollisions_iff.mp hp'.1
  have hqc := mem_canonicalReducedCollisions_iff.mp hp'.2.1
  rcases distinct_canonicalReducedCollisions_positive_negative_cross
      g hg hh hh0 p.1 p.2 hrc hqc (Ne.symm hp'.2.2) with
    hforward | hreverse
  · exact Or.inl
      ((mem_canonicalPositiveNegativeCrossPairs_iff).mpr
        ⟨hp'.1, hp'.2.1, hp'.2.2, hforward⟩)
  · apply Or.inr
    apply Finset.mem_image.mpr
    refine ⟨(p.2, p.1), ?_, by rcases p; rfl⟩
    exact (mem_canonicalPositiveNegativeCrossPairs_iff).mpr
      ⟨hp'.2.1, hp'.1, Ne.symm hp'.2.2, hreverse⟩

/-- Quantitative density: oriented positive/negative crossings occupy at
least half of all ordered distinct canonical pairs. -/
theorem card_canonicalDistinctPairs_le_two_mul_crossPairs
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (canonicalDistinctReducedCollisionPairs (g := g) hh).card ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).card := by
  classical
  have hcover :
      canonicalDistinctReducedCollisionPairs (g := g) hh ⊆
        canonicalPositiveNegativeCrossPairs (g := g) hh ∪
          reversedCanonicalPositiveNegativeCrossPairs (g := g) hh := by
    intro p hp
    rcases mem_cross_or_reverse_of_mem_canonicalDistinctPairs
        g hg hh hh0 hp with hpCross | hpReverse
    · exact Finset.mem_union_left _ hpCross
    · exact Finset.mem_union_right _ hpReverse
  have hsub := Finset.card_le_card
    hcover
  have hunion := Finset.card_union_le
    (canonicalPositiveNegativeCrossPairs (g := g) hh)
    (reversedCanonicalPositiveNegativeCrossPairs (g := g) hh)
  have hreverse :
      (reversedCanonicalPositiveNegativeCrossPairs (g := g) hh).card ≤
        (canonicalPositiveNegativeCrossPairs (g := g) hh).card := by
    unfold reversedCanonicalPositiveNegativeCrossPairs
    exact Finset.card_image_le
  omega

/-- Weighted density: reversal preserves the product of the exact padding
weights, so the crossing relation captures at least half of the total product
weight on ordered distinct canonical pairs. -/
theorem sum_canonicalDistinctPairWeights_le_two_mul_crossPairWeights
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (canonicalDistinctReducedCollisionPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) ≤
      2 * (canonicalPositiveNegativeCrossPairs (g := g) hh).sum (fun p ↦
        reducedCollisionWeight (m := m) p.1 *
          reducedCollisionWeight (m := m) p.2) := by
  classical
  let cross := canonicalPositiveNegativeCrossPairs (g := g) hh
  let reverse := reversedCanonicalPositiveNegativeCrossPairs (g := g) hh
  let weight : ReducedSubsetSumCollision g h ×
      ReducedSubsetSumCollision g h → ℕ := fun p ↦
    reducedCollisionWeight (m := m) p.1 *
      reducedCollisionWeight (m := m) p.2
  have hcover :
      canonicalDistinctReducedCollisionPairs (g := g) hh ⊆ cross ∪ reverse := by
    intro p hp
    rcases mem_cross_or_reverse_of_mem_canonicalDistinctPairs
        g hg hh hh0 hp with hpCross | hpReverse
    · exact Finset.mem_union_left _ hpCross
    · exact Finset.mem_union_right _ hpReverse
  have hsub :
      (canonicalDistinctReducedCollisionPairs (g := g) hh).sum weight ≤
        (cross ∪ reverse).sum weight :=
    Finset.sum_le_sum_of_subset hcover
  have hunion :
      (cross ∪ reverse).sum weight ≤ cross.sum weight + reverse.sum weight := by
    have hidentity := Finset.sum_union_inter
      (s₁ := cross) (s₂ := reverse) (f := weight)
    calc
      (cross ∪ reverse).sum weight ≤
          (cross ∪ reverse).sum weight + (cross ∩ reverse).sum weight := by
        omega
      _ = cross.sum weight + reverse.sum weight := hidentity
  have hreverse : reverse.sum weight = cross.sum weight := by
    dsimp [reverse, reversedCanonicalPositiveNegativeCrossPairs]
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro p hp
      simp [weight, Nat.mul_comm]
    · intro p hp q hq hpq
      apply Prod.ext
      · exact congrArg Prod.snd hpq
      · exact congrArg Prod.fst hpq
  change (canonicalDistinctReducedCollisionPairs (g := g) hh).sum weight ≤
    2 * cross.sum weight
  calc
    (canonicalDistinctReducedCollisionPairs (g := g) hh).sum weight ≤
        (cross ∪ reverse).sum weight := hsub
    _ ≤ cross.sum weight + reverse.sum weight := hunion
    _ = 2 * cross.sum weight := by rw [hreverse]; omega

end MinModulus
