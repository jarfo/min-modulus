/-
# Realizing escape depth as a finite padding cube

`G1EscapeDepth` proves numerically that a target of support depth `d` loses
exactly a factor `2^d` of padding weight.  This file realizes that factor as
an actual finite cube.  We select `d` coordinates from the target support
outside the dominant support, allow an arbitrary subset of those coordinates,
and pair it with an arbitrary legal padding of the target.

The resulting restored target layer has exactly the dominant collision's
padding cardinality.  Its ordinary subset map is injective: the restoration
choice is recovered inside the target support, while the target padding is
recovered outside it.  Validity therefore makes the associated group-value
map injective as well.  This replaces the formal multiplier `2^d` by a
concrete full-size subset-sum layer whose intersections can be studied next.
-/
import MinModulus.G1EscapeDepth

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- There are enough external target coordinates to select exactly the net
support depth. -/
theorem exists_restorationSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    ∃ K ⊆ reducedCollisionExternalSupport r q,
      K.card = reducedCollisionSupportDepth r q := by
  have hexact :=
    card_externalSupport_eq_card_droppedSupport_add_depth r q hcard
  have hdepth : reducedCollisionSupportDepth r q ≤
      (reducedCollisionExternalSupport r q).card := by omega
  exact Finset.exists_subset_card_eq hdepth

/-- A fixed depth-sized set of external target coordinates.  No canonical
choice is needed; only its containment and cardinality are used. -/
noncomputable def reducedCollisionRestorationSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Fin m) := by
  classical
  exact if hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card then
    Classical.choose (exists_restorationSupport r q hcard)
  else ∅

omit [DecidableEq G] in
theorem restorationSupport_subset_external
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    reducedCollisionRestorationSupport r q ⊆
      reducedCollisionExternalSupport r q := by
  classical
  rw [reducedCollisionRestorationSupport, dif_pos hcard]
  exact (Classical.choose_spec
    (exists_restorationSupport r q hcard)).1

omit [DecidableEq G] in
theorem card_restorationSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    (reducedCollisionRestorationSupport r q).card =
      reducedCollisionSupportDepth r q := by
  classical
  rw [reducedCollisionRestorationSupport, dif_pos hcard]
  exact (Classical.choose_spec
    (exists_restorationSupport r q hcard)).2

/-- One choice in the restoration cube. -/
def CollisionRestorationChoice
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :=
  {V : Finset (Fin m) // V ⊆ reducedCollisionRestorationSupport r q}

/-- A restored target object consists of a restoration-cube choice and a
legal common padding of the target collision. -/
def RestoredCollisionPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :=
  CollisionRestorationChoice r q × CollisionPadding q

noncomputable instance instFintypeCollisionRestorationChoice
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    Fintype (CollisionRestorationChoice r q) := by
  unfold CollisionRestorationChoice
  infer_instance

noncomputable instance instFintypeRestoredCollisionPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    Fintype (RestoredCollisionPadding r q) := by
  unfold RestoredCollisionPadding
  infer_instance

omit [DecidableEq G] in
/-- The selected restoration coordinates contribute exactly `2^d` choices. -/
theorem card_collisionRestorationChoice
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    Fintype.card (CollisionRestorationChoice r q) =
      2 ^ reducedCollisionSupportDepth r q := by
  classical
  change Fintype.card
      {V : Finset (Fin m) //
        V ⊆ reducedCollisionRestorationSupport r q} =
    2 ^ reducedCollisionSupportDepth r q
  rw [Fintype.card_subtype]
  have hfilter :
      Finset.univ.filter (fun V : Finset (Fin m) ↦
          V ⊆ reducedCollisionRestorationSupport r q) =
        (reducedCollisionRestorationSupport r q).powerset := by
    ext V
    simp
  rw [hfilter, Finset.card_powerset, card_restorationSupport r q hcard]

omit [DecidableEq G] in
/-- The restored target layer has exactly the source collision's full padding
cardinality. -/
theorem card_restoredCollisionPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    Fintype.card (RestoredCollisionPadding r q) =
      reducedCollisionWeight (m := m) r := by
  change Fintype.card
      (CollisionRestorationChoice r q × CollisionPadding q) = _
  rw [Fintype.card_prod,
    card_collisionRestorationChoice r q hcard,
    card_collisionPadding q]
  exact (reducedCollisionWeight_eq_pow_depth_mul r q hcard).symm

/-- Forget the two factors and view a restored target object as one ordinary
tail-coordinate subset. -/
def restoredCollisionSubset
    {g : Fin (m + 1) → G} {h : G}
    {r q : ReducedSubsetSumCollision g h}
    (x : RestoredCollisionPadding r q) : Finset (Fin m) :=
  x.1.val ∪ x.2.val

omit [DecidableEq G] in
/-- Restoration choices lie inside the target support. -/
theorem restorationChoice_subset_targetSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (V : CollisionRestorationChoice r q) :
    V.val ⊆ reducedCollisionSupport q := by
  exact V.property.trans <|
    (restorationSupport_subset_external r q hcard).trans
      Finset.sdiff_subset

omit [DecidableEq G] in
/-- Target padding lies outside the target support. -/
theorem collisionPadding_disjoint_support
    {g : Fin (m + 1) → G} {h : G}
    (q : ReducedSubsetSumCollision g h) (U : CollisionPadding q) :
    Disjoint U.val (reducedCollisionSupport q) := by
  rw [Finset.disjoint_left]
  intro k hkU hkq
  exact (Finset.mem_sdiff.mp (U.property hkU)).2 <| by
    simpa [reducedCollisionSupport] using hkq

omit [DecidableEq G] in
/-- The ordinary subset remembers both factors: intersecting with the target
support recovers the restoration choice, and the complement recovers the
legal target padding. -/
theorem restoredCollisionSubset_injective
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    Function.Injective
      (restoredCollisionSubset (r := r) (q := q)) := by
  intro x y hxy
  apply Prod.ext
  · apply Subtype.ext
    apply Finset.Subset.antisymm
    · intro k hk
      have hkq := restorationChoice_subset_targetSupport r q hcard x.1 hk
      have hky : k ∈ restoredCollisionSubset y := by
        rw [← hxy]
        exact Finset.mem_union_left _ hk
      rcases Finset.mem_union.mp hky with hkyV | hkyU
      · exact hkyV
      · exact False.elim
          (Finset.disjoint_left.mp (collisionPadding_disjoint_support q y.2)
            hkyU hkq)
    · intro k hk
      have hkq := restorationChoice_subset_targetSupport r q hcard y.1 hk
      have hkx : k ∈ restoredCollisionSubset x := by
        rw [hxy]
        exact Finset.mem_union_left _ hk
      rcases Finset.mem_union.mp hkx with hkxV | hkxU
      · exact hkxV
      · exact False.elim
          (Finset.disjoint_left.mp (collisionPadding_disjoint_support q x.2)
            hkxU hkq)
  · apply Subtype.ext
    apply Finset.Subset.antisymm
    · intro k hk
      have hknotq : k ∉ reducedCollisionSupport q := fun hkq ↦
        Finset.disjoint_left.mp (collisionPadding_disjoint_support q x.2)
          hk hkq
      have hky : k ∈ restoredCollisionSubset y := by
        rw [← hxy]
        exact Finset.mem_union_right _ hk
      rcases Finset.mem_union.mp hky with hkyV | hkyU
      · exact False.elim (hknotq
          (restorationChoice_subset_targetSupport r q hcard y.1 hkyV))
      · exact hkyU
    · intro k hk
      have hknotq : k ∉ reducedCollisionSupport q := fun hkq ↦
        Finset.disjoint_left.mp (collisionPadding_disjoint_support q y.2)
          hk hkq
      have hkx : k ∈ restoredCollisionSubset x := by
        rw [hxy]
        exact Finset.mem_union_right _ hk
      rcases Finset.mem_union.mp hkx with hkxV | hkxU
      · exact False.elim (hknotq
          (restorationChoice_subset_targetSupport r q hcard x.1 hkxV))
      · exact hkxU

/-- Group value associated to an object of the restored target layer. -/
def restoredCollisionValue
    {g : Fin (m + 1) → G} {h : G}
    {r q : ReducedSubsetSumCollision g h}
    (x : RestoredCollisionPadding r q) : G :=
  ssum g (restoredCollisionSubset x)

omit [DecidableEq G] in
/-- Validity makes all values in one restored target layer distinct. -/
theorem restoredCollisionValue_injective
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    Function.Injective
      (restoredCollisionValue (g := g) (r := r) (q := q)) := by
  intro x y hxy
  apply restoredCollisionSubset_injective r q hcard
  exact ssum_injective g hg hxy

/-- The concrete group-value image of a restored target layer. -/
noncomputable def restoredCollisionValueLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset G := by
  classical
  exact Finset.univ.image
    (restoredCollisionValue (g := g) (r := r) (q := q))

/-- Every strictly growing target supplies a concrete subset-sum value layer
whose cardinality equals the dominant source's full padding weight. -/
theorem card_restoredCollisionValueLayer
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    (restoredCollisionValueLayer r q).card =
      reducedCollisionWeight (m := m) r := by
  classical
  rw [restoredCollisionValueLayer,
    Finset.card_image_of_injective _
      (restoredCollisionValue_injective hg r q hcard),
    Finset.card_univ, card_restoredCollisionPadding r q hcard]

/-- The restored values are an explicit sublayer of the anchored subset-sum
cube. -/
theorem restoredCollisionValueLayer_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    restoredCollisionValueLayer r q ⊆ subsetSumRange g := by
  classical
  intro x hx
  rw [restoredCollisionValueLayer] at hx
  rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
  rw [subsetSumRange]
  exact Finset.mem_image.mpr
    ⟨restoredCollisionSubset p, Finset.mem_univ _, rfl⟩

/-- Concrete package saying that a target's lost padding dimensions have been
restored as a full source-sized subset-sum value layer. -/
def IsFullRestoredCollisionLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Prop :=
  reducedCollisionRestorationSupport r q ⊆
      reducedCollisionExternalSupport r q ∧
    (reducedCollisionRestorationSupport r q).card =
      reducedCollisionSupportDepth r q ∧
    (restoredCollisionValueLayer r q).card =
      reducedCollisionWeight (m := m) r ∧
    restoredCollisionValueLayer r q ⊆ subsetSumRange g

/-- Any target of no smaller support has a full restored collision layer. -/
theorem isFullRestoredCollisionLayer_of_support_card_le
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    IsFullRestoredCollisionLayer r q := by
  exact ⟨restorationSupport_subset_external r q hcard,
    card_restorationSupport r q hcard,
    card_restoredCollisionValueLayer hg r q hcard,
    restoredCollisionValueLayer_subset_subsetSumRange r q⟩

/-- In the strict-majority branch, every non-root canonical target carries
one concrete full dominant-weight restored layer. -/
theorem canonical_other_isFullRestoredCollisionLayer_of_strictMajority
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g) (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    ∀ q ∈ canonicalReducedCollisions (g := g) hh, q ≠ r →
      IsFullRestoredCollisionLayer r q := by
  intro q hq hqr
  have hgrowth := canonical_other_support_growth_of_strictMajority
    hh r hr hmajor q hq hqr
  apply isFullRestoredCollisionLayer_of_support_card_le hg r q
  simpa [reducedCollisionSupport] using hgrowth.1.le

end MinModulus
