/-
# Intersection structure of reduced critical collisions

The exact padding formula reduces the overlap count to disjoint witness
shapes `(A,B)`.  This file applies witness combination directly to those
shapes.  After orienting them by `|A| ≤ |B|`, the negative tails of any two
shapes intersect unless the shapes are exact swaps of one another.  The swap
is a fixed-point-free involution and preserves the padding weight.  If one
shape is strictly unbalanced, even this swap exception is impossible.

Thus the weighted reduced family is an intersecting family up to explicit,
equal-weight opposite pairs—the precise combinatorial input needed after the
padding decomposition.
-/
import MinModulus.G1OverlapPadding

namespace MinModulus

open Finset

variable {m : ℕ}

/-- For disjoint pairs, negating a collision coefficient vector uniquely
swaps its positive and negative tail sets. -/
theorem subsetCollisionCoeffs_eq_neg_of_disjoint_imp_swap
    {A₁ B₁ A₂ B₂ : Finset (Fin m)}
    (hd₁ : Disjoint A₁ B₁) (hd₂ : Disjoint A₂ B₂)
    (hcoeff : subsetCollisionCoeffs A₂ B₂ =
      -subsetCollisionCoeffs A₁ B₁) :
    A₂ = B₁ ∧ B₂ = A₁ := by
  have hd₁' := Finset.disjoint_left.mp hd₁
  have hd₂' := Finset.disjoint_left.mp hd₂
  constructor <;> ext j
  · have hv := congrFun hcoeff j.succ
    simp only [Pi.neg_apply, subsetCollisionCoeffs, Fin.cons_succ] at hv
    by_cases hA₁ : j ∈ A₁ <;> by_cases hB₁ : j ∈ B₁ <;>
      by_cases hA₂ : j ∈ A₂ <;> by_cases hB₂ : j ∈ B₂ <;>
      simp_all
  · have hv := congrFun hcoeff j.succ
    simp only [Pi.neg_apply, subsetCollisionCoeffs, Fin.cons_succ] at hv
    by_cases hA₁ : j ∈ A₁ <;> by_cases hB₁ : j ∈ B₁ <;>
      by_cases hA₂ : j ∈ A₂ <;> by_cases hB₂ : j ∈ B₂ <;>
      simp_all

variable {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
lemma reducedSubsetSumCollision_reverse_value
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    ssum g r.val.2 = ssum g r.val.1 + h :=
  subsetSumCollision_reverse_value hh ⟨r.val, r.property.2⟩

omit [DecidableEq G] in
/-- Swap the two sides of every reduced collision at an order-two target. -/
def reducedSubsetSumCollisionSwapEquiv
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) :
    ReducedSubsetSumCollision g h ≃ ReducedSubsetSumCollision g h where
  toFun r := ⟨(r.val.2, r.val.1),
    ⟨r.property.1.symm, reducedSubsetSumCollision_reverse_value hh r⟩⟩
  invFun r := ⟨(r.val.2, r.val.1),
    ⟨r.property.1.symm, reducedSubsetSumCollision_reverse_value hh r⟩⟩
  left_inv r := by rfl
  right_inv r := by rfl

omit [DecidableEq G] in
/-- The reduced swap has no fixed point at a nonzero target. -/
theorem reducedSubsetSumCollisionSwapEquiv_ne
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h) :
    reducedSubsetSumCollisionSwapEquiv hh r ≠ r := by
  intro hr
  have hpairs := congrArg Subtype.val hr
  have hBA : r.val.2 = r.val.1 := congrArg Prod.fst hpairs
  apply hh0
  apply add_left_cancel (a := ssum g r.val.1)
  simpa [hBA] using r.property.2.symm

omit [DecidableEq G] in
/-- Orient a reduced collision so that its anchor coefficient is
nonnegative. -/
def orientReducedSubsetSumCollision
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : ReducedSubsetSumCollision g h :=
  if r.val.1.card ≤ r.val.2.card then r
  else reducedSubsetSumCollisionSwapEquiv hh r

omit [DecidableEq G] in
theorem orientReducedSubsetSumCollision_card_le
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    (orientReducedSubsetSumCollision hh r).val.1.card ≤
      (orientReducedSubsetSumCollision hh r).val.2.card := by
  by_cases hcard : r.val.1.card ≤ r.val.2.card
  · simp [orientReducedSubsetSumCollision, hcard]
  · have hrev : r.val.2.card ≤ r.val.1.card := Nat.le_of_lt (Nat.lt_of_not_ge hcard)
    simpa [orientReducedSubsetSumCollision, hcard,
      reducedSubsetSumCollisionSwapEquiv] using hrev

omit [DecidableEq G] in
/-- Witness combination on two oriented reduced collisions: disjoint negative
tails force their coefficient vectors to be exact negatives. -/
theorem reducedCollision_negative_inter_or_coeff_neg
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r₁ r₂ : ReducedSubsetSumCollision g h)
    (hcard₁ : r₁.val.1.card ≤ r₁.val.2.card)
    (hcard₂ : r₂.val.1.card ≤ r₂.val.2.card) :
    (r₁.val.2 ∩ r₂.val.2).Nonempty ∨
      subsetCollisionCoeffs r₂.val.1 r₂.val.2 =
        -subsetCollisionCoeffs r₁.val.1 r₁.val.2 := by
  by_cases hinter : (r₁.val.2 ∩ r₂.val.2).Nonempty
  · exact Or.inl hinter
  · right
    have hc₁ := witness_of_subsetSum_eq_add g hh0 hcard₁ r₁.property.2
    have hc₂ := witness_of_subsetSum_eq_add g hh0 hcard₂ r₂.property.2
    apply witness_combination g hg hh hc₁ hc₂
    intro i
    refine Fin.cases ?_ ?_ i
    · intro hi
      have hge := subsetCollisionCoeffs_ge_neg_one
        r₁.val.1 r₁.val.2 hcard₁ 0
      simp only [subsetCollisionCoeffs, Fin.cons_zero] at hge hi
      omega
    · intro j hj
      have hj₁ := (subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
        r₁.val.1 r₁.val.2 j).mp hj.1
      have hj₂ := (subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
        r₂.val.1 r₂.val.2 j).mp hj.2
      apply hinter
      exact ⟨j, Finset.mem_inter.mpr
        ⟨(Finset.mem_sdiff.mp hj₁).1, (Finset.mem_sdiff.mp hj₂).1⟩⟩

omit [DecidableEq G] in
/-- The negative-tail exception from witness combination is exactly a swap
of the two disjoint reduced pairs. -/
theorem reducedCollision_negative_tails_inter_or_swapped
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r₁ r₂ : ReducedSubsetSumCollision g h)
    (hcard₁ : r₁.val.1.card ≤ r₁.val.2.card)
    (hcard₂ : r₂.val.1.card ≤ r₂.val.2.card) :
    (r₁.val.2 ∩ r₂.val.2).Nonempty ∨
      (r₂.val.1 = r₁.val.2 ∧ r₂.val.2 = r₁.val.1) := by
  rcases reducedCollision_negative_inter_or_coeff_neg
      g hg hh hh0 r₁ r₂ hcard₁ hcard₂ with hinter | hneg
  · exact Or.inl hinter
  · exact Or.inr (subsetCollisionCoeffs_eq_neg_of_disjoint_imp_swap
      r₁.property.1 r₂.property.1 hneg)

omit [DecidableEq G] in
/-- Equivalence-valued version of the reduced intersection-or-swap
dichotomy. -/
theorem reducedCollision_negative_tails_inter_or_eq_swap
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r₁ r₂ : ReducedSubsetSumCollision g h)
    (hcard₁ : r₁.val.1.card ≤ r₁.val.2.card)
    (hcard₂ : r₂.val.1.card ≤ r₂.val.2.card) :
    (r₁.val.2 ∩ r₂.val.2).Nonempty ∨
      r₂ = reducedSubsetSumCollisionSwapEquiv hh r₁ := by
  rcases reducedCollision_negative_tails_inter_or_swapped
      g hg hh hh0 r₁ r₂ hcard₁ hcard₂ with hinter | hswap
  · exact Or.inl hinter
  · right
    apply Subtype.ext
    apply Prod.ext
    · exact hswap.1
    · exact hswap.2

omit [DecidableEq G] in
/-- A strictly unbalanced oriented reduced shape has intersecting negative
tail with every oriented reduced shape; the swap exception cannot occur. -/
theorem reducedCollision_negative_tails_inter_of_card_lt
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r₁ r₂ : ReducedSubsetSumCollision g h)
    (hlt₁ : r₁.val.1.card < r₁.val.2.card)
    (hcard₂ : r₂.val.1.card ≤ r₂.val.2.card) :
    (r₁.val.2 ∩ r₂.val.2).Nonempty := by
  rcases reducedCollision_negative_tails_inter_or_swapped
      g hg hh hh0 r₁ r₂ hlt₁.le hcard₂ with hinter | hswap
  · exact hinter
  · have hrev : r₁.val.2.card ≤ r₁.val.1.card := by
      rw [← hswap.1, ← hswap.2]
      exact hcard₂
    omega

omit [DecidableEq G] in
/-- Exact swapped exceptions carry equal padding weights. -/
theorem reducedCollision_swapped_weight
    {g : Fin (m + 1) → G} {h : G}
    {r₁ r₂ : ReducedSubsetSumCollision g h}
    (hswap : r₂.val.1 = r₁.val.2 ∧ r₂.val.2 = r₁.val.1) :
    2 ^ (m - (r₂.val.1 ∪ r₂.val.2).card) =
      2 ^ (m - (r₁.val.1 ∪ r₁.val.2).card) := by
  rw [hswap.1, hswap.2, Finset.union_comm]

end MinModulus
