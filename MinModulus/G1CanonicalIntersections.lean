/-
# Canonical intersecting representatives of reduced collisions

Reduced half-collisions are paired by the fixed-point-free swap `(A,B) ↔
(B,A)`.  This file selects exactly one representative from every pair:
strictly unbalanced pairs use the cardinality orientation, while balanced
pairs use a finite code as a tie-breaker.

Witness combination then shows that the negative tails of the selected
representatives are pairwise intersecting.  Since swap preserves the exact
padding weight, the total reduced-collision weight is exactly twice the
weight of this canonical intersecting family.
-/
import MinModulus.G1ReducedIntersections

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- An arbitrary finite code used only to orient balanced swap pairs. -/
noncomputable def reducedCollisionCode {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) :
    Fin (Fintype.card (ReducedSubsetSumCollision g h)) :=
  Fintype.equivFin (ReducedSubsetSumCollision g h) r

/-- A collision and its nontrivial swap have different finite codes. -/
theorem reducedCollisionCode_ne_swap
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h) :
    reducedCollisionCode r ≠
      reducedCollisionCode (reducedSubsetSumCollisionSwapEquiv hh r) := by
  intro heq
  apply reducedSubsetSumCollisionSwapEquiv_ne hh hh0 r
  exact (Fintype.equivFin (ReducedSubsetSumCollision g h)).injective heq.symm

/-- Canonical orientation of a reduced collision.  Strictly unbalanced pairs
use cardinality; balanced pairs use the finite code. -/
noncomputable def IsCanonicalReducedCollision
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) : Prop :=
  r.val.1.card < r.val.2.card ∨
    (r.val.1.card = r.val.2.card ∧
      reducedCollisionCode r <
        reducedCollisionCode (reducedSubsetSumCollisionSwapEquiv hh r))

theorem canonicalReducedCollision_card_le
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r : ReducedSubsetSumCollision g h}
    (hr : IsCanonicalReducedCollision hh r) :
    r.val.1.card ≤ r.val.2.card := by
  rcases hr with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

/-- Exactly one member of each nontrivial swap pair is canonical. -/
theorem canonicalReducedCollision_swap_iff_not
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (r : ReducedSubsetSumCollision g h) :
    IsCanonicalReducedCollision hh (reducedSubsetSumCollisionSwapEquiv hh r) ↔
      ¬IsCanonicalReducedCollision hh r := by
  have hcode := reducedCollisionCode_ne_swap hh hh0 r
  change
    (r.val.2.card < r.val.1.card ∨
      (r.val.2.card = r.val.1.card ∧
        reducedCollisionCode (reducedSubsetSumCollisionSwapEquiv hh r) <
          reducedCollisionCode r)) ↔
      ¬(r.val.1.card < r.val.2.card ∨
        (r.val.1.card = r.val.2.card ∧
          reducedCollisionCode r <
            reducedCollisionCode (reducedSubsetSumCollisionSwapEquiv hh r)))
  omega

/-- The canonical negative tails form a genuinely pairwise-intersecting
family: the exact-swap exception cannot contain two canonical members. -/
theorem canonicalReducedCollision_negative_tails_inter
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0)
    (r₁ r₂ : ReducedSubsetSumCollision g h)
    (hc₁ : IsCanonicalReducedCollision hh r₁)
    (hc₂ : IsCanonicalReducedCollision hh r₂) :
    (r₁.val.2 ∩ r₂.val.2).Nonempty := by
  rcases reducedCollision_negative_tails_inter_or_eq_swap
      g hg hh hh0 r₁ r₂
      (canonicalReducedCollision_card_le hc₁)
      (canonicalReducedCollision_card_le hc₂) with hinter | hswap
  · exact hinter
  · rw [hswap] at hc₂
    exact False.elim
      ((canonicalReducedCollision_swap_iff_not hh hh0 r₁).mp hc₂ hc₁)

/-- The finite family containing the canonical member of every swap pair. -/
noncomputable def canonicalReducedCollisions
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) :
    Finset (ReducedSubsetSumCollision g h) := by
  classical
  exact Finset.univ.filter (IsCanonicalReducedCollision hh)

@[simp] theorem mem_canonicalReducedCollisions_iff
    {g : Fin (m + 1) → G} {h : G} {hh : h + h = 0}
    {r : ReducedSubsetSumCollision g h} :
    r ∈ canonicalReducedCollisions hh ↔
      IsCanonicalReducedCollision hh r := by
  classical
  simp [canonicalReducedCollisions]

noncomputable def noncanonicalReducedCollisions
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) :
    Finset (ReducedSubsetSumCollision g h) := by
  classical
  exact Finset.univ.filter (fun r ↦ ¬IsCanonicalReducedCollision hh r)

noncomputable def swappedCanonicalReducedCollisions
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) :
    Finset (ReducedSubsetSumCollision g h) := by
  classical
  exact (canonicalReducedCollisions hh).image
    (reducedSubsetSumCollisionSwapEquiv hh)

/-- Swapping the canonical family gives exactly its complement. -/
theorem swappedCanonicalReducedCollisions_eq_noncanonical
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) (hh0 : h ≠ 0) :
    swappedCanonicalReducedCollisions (g := g) hh =
      noncanonicalReducedCollisions hh := by
  classical
  unfold swappedCanonicalReducedCollisions noncanonicalReducedCollisions
  ext r
  simp only [Finset.mem_image, mem_canonicalReducedCollisions_iff,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, hqr⟩
    rw [← hqr]
    intro hswap
    exact (canonicalReducedCollision_swap_iff_not hh hh0 q).mp hswap hq
  · intro hr
    refine ⟨reducedSubsetSumCollisionSwapEquiv hh r, ?_, ?_⟩
    · exact (canonicalReducedCollision_swap_iff_not hh hh0 r).mpr hr
    · rfl

/-- Exact padding multiplicity attached to a reduced collision shape. -/
def reducedCollisionWeight {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) : ℕ :=
  2 ^ (m - (r.val.1 ∪ r.val.2).card)

omit [DecidableEq G] in
theorem reducedCollisionWeight_swap
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    reducedCollisionWeight (reducedSubsetSumCollisionSwapEquiv hh r) =
      reducedCollisionWeight r := by
  simp [reducedCollisionWeight, reducedSubsetSumCollisionSwapEquiv,
    Finset.union_comm]

/-- The total reduced-collision weight is exactly twice the weight carried by
the canonical intersecting representatives. -/
theorem sum_reducedCollisionWeight_eq_two_mul_canonical
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∑ r : ReducedSubsetSumCollision g h, reducedCollisionWeight r) =
      2 * (canonicalReducedCollisions (g := g) hh).sum
        (fun r ↦ reducedCollisionWeight (m := m) r) := by
  classical
  let C := canonicalReducedCollisions (g := g) hh
  let R := noncanonicalReducedCollisions (g := g) hh
  have hR : R.sum reducedCollisionWeight = C.sum reducedCollisionWeight := by
    dsimp [R, C]
    rw [← swappedCanonicalReducedCollisions_eq_noncanonical hh hh0]
    unfold swappedCanonicalReducedCollisions
    rw [Finset.sum_image
      (reducedSubsetSumCollisionSwapEquiv hh).injective.injOn]
    apply Finset.sum_congr rfl
    intro r _
    exact reducedCollisionWeight_swap hh r
  calc
    (∑ r : ReducedSubsetSumCollision g h, reducedCollisionWeight r) =
        C.sum reducedCollisionWeight + R.sum reducedCollisionWeight := by
      symm
      simpa [C, R, canonicalReducedCollisions,
        noncanonicalReducedCollisions] using
        Finset.sum_filter_add_sum_filter_not
        (Finset.univ : Finset (ReducedSubsetSumCollision g h))
        (IsCanonicalReducedCollision hh) reducedCollisionWeight
    _ = 2 * C.sum reducedCollisionWeight := by
      rw [hR, two_mul]

/-- For a valid tuple, the entire half-translate overlap is twice the exact
padding weight of the canonical intersecting representatives. -/
theorem card_subsetSumOverlap_eq_two_mul_canonical_weights
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card =
      2 * (canonicalReducedCollisions (g := g) hh).sum
        (fun r ↦ reducedCollisionWeight (m := m) r) := by
  rw [card_subsetSumOverlap_eq_sum_reduced_weights g hg h]
  simpa [reducedCollisionWeight] using
    sum_reducedCollisionWeight_eq_two_mul_canonical
      (g := g) hh hh0

end MinModulus
