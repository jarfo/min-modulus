/-
# Reduced overlap collisions and exact padding multiplicities

An ordered overlap collision `(S,T)` may contain an arbitrary common subset:
adding the same padding `U` to both sides does not change its coefficient
vector.  This file removes that multiplicity exactly.

Every collision is uniquely equivalent to a disjoint reduced relation
`(S \ T, T \ S)` together with a padding subset of the complement of its
tail support.  A reduced shape with tail support `A ∪ B` therefore occurs
exactly `2^(m-|A ∪ B|)` times.  For a valid tuple, the cardinality of the
entire translated-cube overlap is the sum of these exact weights over all
reduced witness shapes.
-/
import MinModulus.G1OverlapSupports

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]
variable {g : Fin (m + 1) → G} {h : G}

omit [DecidableEq G] in
/-- Split a subset sum into its part outside `T` and its intersection with
`T`. -/
lemma ssum_sdiff_add_inter (g : Fin (m + 1) → G)
    (S T : Finset (Fin m)) :
    ssum g (S \ T) + ssum g (S ∩ T) = ssum g S := by
  unfold ssum
  rw [← Finset.sum_union (Finset.disjoint_sdiff_inter _ _),
    Finset.sdiff_union_inter]

omit [DecidableEq G] in
/-- Cancelling the common subset of an ordered collision preserves its
half-shift relation. -/
lemma subsetSumCollision_reduced_value
    {g : Fin (m + 1) → G} {h : G} (p : SubsetSumCollision g h) :
    ssum g (p.val.1 \ p.val.2) =
      ssum g (p.val.2 \ p.val.1) + h := by
  apply add_right_cancel (b := ssum g (p.val.1 ∩ p.val.2))
  calc
    ssum g (p.val.1 \ p.val.2) + ssum g (p.val.1 ∩ p.val.2) =
        ssum g p.val.1 := ssum_sdiff_add_inter g _ _
    _ = ssum g p.val.2 + h := p.property
    _ = (ssum g (p.val.2 \ p.val.1) +
          ssum g (p.val.2 ∩ p.val.1)) + h := by
      rw [← ssum_sdiff_add_inter g p.val.2 p.val.1]
    _ = (ssum g (p.val.2 \ p.val.1) + h) +
          ssum g (p.val.1 ∩ p.val.2) := by
      rw [Finset.inter_comm p.val.2 p.val.1]
      abel

/-- A reduced collision is an ordered half-shift relation between disjoint
subsets. -/
def ReducedSubsetSumCollision (g : Fin (m + 1) → G) (h : G) :=
  {p : Finset (Fin m) × Finset (Fin m) //
    Disjoint p.1 p.2 ∧ ssum g p.1 = ssum g p.2 + h}

/-- Common padding may use any coordinate outside a reduced collision's tail
support. -/
def CollisionPadding {g : Fin (m + 1) → G} {h : G}
    (p : ReducedSubsetSumCollision g h) :=
  {U : Finset (Fin m) // U ⊆ Finset.univ \ (p.val.1 ∪ p.val.2)}

/-- Remove the common intersection from an ordered collision. -/
def subsetSumCollisionReduced (p : SubsetSumCollision g h) :
    ReducedSubsetSumCollision g h :=
  ⟨(p.val.1 \ p.val.2, p.val.2 \ p.val.1), by
    constructor
    · rw [Finset.disjoint_left]
      intro x hxS hxT
      exact (Finset.mem_sdiff.mp hxT).2 (Finset.mem_sdiff.mp hxS).1
    · exact subsetSumCollision_reduced_value p⟩

/-- Cancelling common padding leaves the collision coefficient vector
unchanged. -/
theorem subsetCollisionCoeffs_reduce (S T : Finset (Fin m)) :
    subsetCollisionCoeffs (S \ T) (T \ S) = subsetCollisionCoeffs S T := by
  funext i
  refine Fin.cases ?_ ?_ i
  · have hS := Finset.card_sdiff_add_card_inter S T
    have hT := Finset.card_sdiff_add_card_inter T S
    rw [Finset.inter_comm T S] at hT
    simp only [subsetCollisionCoeffs, Fin.cons_zero]
    omega
  · intro j
    by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;>
      simp [subsetCollisionCoeffs, hS, hT]

/-- Extract the common intersection as legal padding of the reduced
collision. -/
def subsetSumCollisionPadding (p : SubsetSumCollision g h) :
    CollisionPadding (subsetSumCollisionReduced p) :=
  ⟨p.val.1 ∩ p.val.2, by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_union, not_or]
    have hxS := (Finset.mem_inter.mp hx).1
    have hxT := (Finset.mem_inter.mp hx).2
    exact ⟨fun h => (Finset.mem_sdiff.mp h).2 hxT,
      fun h => (Finset.mem_sdiff.mp h).2 hxS⟩⟩

/-- Forward map from an arbitrary collision to its reduced shape and common
padding. -/
def subsetSumCollisionToReducedPadding (p : SubsetSumCollision g h) :
    Σ r : ReducedSubsetSumCollision g h, CollisionPadding r :=
  ⟨subsetSumCollisionReduced p, subsetSumCollisionPadding p⟩

omit [DecidableEq G] in
lemma ssum_union_of_disjoint (g : Fin (m + 1) → G)
    {A U : Finset (Fin m)} (hdisj : Disjoint A U) :
    ssum g (A ∪ U) = ssum g A + ssum g U := by
  unfold ssum
  exact Finset.sum_union hdisj

omit [DecidableEq G] in
lemma collisionPadding_disjoint_left
    (r : ReducedSubsetSumCollision g h) (U : CollisionPadding r) :
    Disjoint r.val.1 U.val := by
  rw [Finset.disjoint_left]
  intro x hxA hxU
  have hxnot := (Finset.mem_sdiff.mp (U.property hxU)).2
  exact hxnot (Finset.mem_union_left _ hxA)

omit [DecidableEq G] in
lemma collisionPadding_disjoint_right
    (r : ReducedSubsetSumCollision g h) (U : CollisionPadding r) :
    Disjoint r.val.2 U.val := by
  rw [Finset.disjoint_left]
  intro x hxB hxU
  have hxnot := (Finset.mem_sdiff.mp (U.property hxU)).2
  exact hxnot (Finset.mem_union_right _ hxB)

/-- Reconstruct an ordered collision by padding both sides of a reduced
relation with the same subset. -/
def reducedPaddingToSubsetSumCollision
    (q : Σ r : ReducedSubsetSumCollision g h, CollisionPadding r) :
    SubsetSumCollision g h :=
  ⟨(q.1.val.1 ∪ q.2.val, q.1.val.2 ∪ q.2.val), by
    rw [ssum_union_of_disjoint g (collisionPadding_disjoint_left q.1 q.2),
      ssum_union_of_disjoint g (collisionPadding_disjoint_right q.1 q.2),
      q.1.property.2]
    abel⟩

omit [DecidableEq G] in
theorem reducedPaddingToSubsetSumCollision_left_inverse :
    Function.LeftInverse
      (reducedPaddingToSubsetSumCollision (g := g) (h := h))
      subsetSumCollisionToReducedPadding := by
  intro p
  apply Subtype.ext
  apply Prod.ext
  · change (p.val.1 \ p.val.2) ∪ (p.val.1 ∩ p.val.2) = p.val.1
    exact Finset.sdiff_union_inter p.val.1 p.val.2
  · change (p.val.2 \ p.val.1) ∪ (p.val.1 ∩ p.val.2) = p.val.2
    rw [Finset.inter_comm p.val.1 p.val.2]
    exact Finset.sdiff_union_inter p.val.2 p.val.1

omit [DecidableEq G] in
theorem reducedPaddingToSubsetSumCollision_right_inverse :
    Function.RightInverse
      (reducedPaddingToSubsetSumCollision (g := g) (h := h))
      subsetSumCollisionToReducedPadding := by
  rintro ⟨r, U⟩
  have hAB := Finset.disjoint_left.mp r.property.1
  have hAU := Finset.disjoint_left.mp (collisionPadding_disjoint_left r U)
  have hBU := Finset.disjoint_left.mp (collisionPadding_disjoint_right r U)
  have hA : (r.val.1 ∪ U.val) \ (r.val.2 ∪ U.val) = r.val.1 := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hxA | hxU, hnot⟩
      · exact hxA
      · exact False.elim (hnot (Or.inr hxU))
    · intro hxA
      refine ⟨Or.inl hxA, ?_⟩
      push Not
      exact ⟨fun hxB => hAB hxA hxB, fun hxU => hAU hxA hxU⟩
  have hB : (r.val.2 ∪ U.val) \ (r.val.1 ∪ U.val) = r.val.2 := by
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_union]
    constructor
    · rintro ⟨hxB | hxU, hnot⟩
      · exact hxB
      · exact False.elim (hnot (Or.inr hxU))
    · intro hxB
      refine ⟨Or.inl hxB, ?_⟩
      push Not
      exact ⟨fun hxA => hAB hxA hxB, fun hxU => hBU hxB hxU⟩
  have hU : (r.val.1 ∪ U.val) ∩ (r.val.2 ∪ U.val) = U.val := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hxA | hxU, hxB | hxU'⟩
      · exact False.elim (hAB hxA hxB)
      · exact hxU'
      · exact hxU
      · exact hxU
    · intro hxU
      exact ⟨Or.inr hxU, Or.inr hxU⟩
  have hr : subsetSumCollisionReduced
      (reducedPaddingToSubsetSumCollision ⟨r, U⟩) = r := by
    apply Subtype.ext
    apply Prod.ext
    · exact hA
    · exact hB
  apply Sigma.ext hr
  refine (Subtype.heq_iff_coe_eq ?_).2 ?_
  · intro V
    change V ⊆ Finset.univ \ ((subsetSumCollisionReduced
        (reducedPaddingToSubsetSumCollision ⟨r, U⟩)).val.1 ∪
          (subsetSumCollisionReduced
            (reducedPaddingToSubsetSumCollision ⟨r, U⟩)).val.2) ↔
      V ⊆ Finset.univ \ (r.val.1 ∪ r.val.2)
    rw [hr]
  · exact hU

/-- Exact decomposition of every ordered collision into a disjoint reduced
collision shape and a common padding subset. -/
def subsetSumCollisionEquivReducedPadding :
    SubsetSumCollision g h ≃
      Σ r : ReducedSubsetSumCollision g h, CollisionPadding r where
  toFun := subsetSumCollisionToReducedPadding
  invFun := reducedPaddingToSubsetSumCollision
  left_inv := reducedPaddingToSubsetSumCollision_left_inverse
  right_inv := reducedPaddingToSubsetSumCollision_right_inverse

noncomputable instance instFintypeReducedSubsetSumCollision :
    Fintype (ReducedSubsetSumCollision g h) := by
  unfold ReducedSubsetSumCollision
  infer_instance

noncomputable instance instFintypeCollisionPadding
    (r : ReducedSubsetSumCollision g h) : Fintype (CollisionPadding r) := by
  unfold CollisionPadding
  infer_instance

omit [DecidableEq G] in
/-- A reduced shape has exactly one padding choice per subset of the
complement of its tail support. -/
theorem card_collisionPadding (r : ReducedSubsetSumCollision g h) :
    Fintype.card (CollisionPadding r) =
      2 ^ (m - (r.val.1 ∪ r.val.2).card) := by
  change Fintype.card
      {U : Finset (Fin m) // U ⊆ Finset.univ \ (r.val.1 ∪ r.val.2)} =
    2 ^ (m - (r.val.1 ∪ r.val.2).card)
  rw [Fintype.card_subtype]
  have hfilter :
      Finset.univ.filter
          (fun U : Finset (Fin m) => U ⊆ Finset.univ \ (r.val.1 ∪ r.val.2)) =
        (Finset.univ \ (r.val.1 ∪ r.val.2)).powerset := by
    ext U
    simp
  rw [hfilter, Finset.card_powerset, Finset.card_sdiff, Finset.inter_univ,
    Finset.card_univ, Fintype.card_fin]

/-- The ordered collision count is the exact padding-weighted sum over
disjoint reduced witness shapes. -/
theorem card_subsetSumCollision_eq_sum_reduced_weights :
    Fintype.card (SubsetSumCollision g h) =
      ∑ r : ReducedSubsetSumCollision g h,
        2 ^ (m - (r.val.1 ∪ r.val.2).card) := by
  rw [Fintype.card_congr subsetSumCollisionEquivReducedPadding,
    Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro r _
  exact card_collisionPadding r

/-- For a valid tuple, the half-translate overlap is exactly the
padding-weighted sum over disjoint reduced witness shapes. -/
theorem card_subsetSumOverlap_eq_sum_reduced_weights
    (g : Fin (m + 1) → G) (hg : ValidTuple g) (h : G) :
    ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card =
      ∑ r : ReducedSubsetSumCollision g h,
        2 ^ (m - (r.val.1 ∪ r.val.2).card) := by
  calc
    ((subsetSumRange g) ∩ (subsetSumShiftRange g h)).card =
        Fintype.card (SubsetSumCollision g h) :=
      (card_subsetSumCollision_eq_card_overlap g hg h).symm
    _ = ∑ r : ReducedSubsetSumCollision g h,
        2 ^ (m - (r.val.1 ∪ r.val.2).card) :=
      card_subsetSumCollision_eq_sum_reduced_weights

end MinModulus
