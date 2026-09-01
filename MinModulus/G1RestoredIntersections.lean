/-
# Intersection of a restored escape layer with the root padding cube

Every growing target now carries a restored subset-sum layer as large as the
dominant root padding cube.  This file computes their first intersection
exactly.  A restored object `(V,U)` lies in the root padding cube precisely
when the target-padding factor `U` also avoids the root support.  Such `U`
are exactly the common paddings outside the union of the two supports.

Consequently the intersection has cardinality

`2^depth * 2^(m - |supp(r) ∪ supp(q)|)`.

For an actual escape incidence, the target padding contains at least one
potential dropped root coordinate.  The exact support-exchange identity then
shows that the intersection is at most half of either full layer.  Thus the
root and every actual restored escape target already occupy a union of at
least `3 w_r / 2` distinct anchored subset-sum values.
-/
import MinModulus.G1RestoredPadding

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Ordinary subsets underlying every legal padding of one collision. -/
noncomputable def collisionPaddingSubsetLayer
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) : Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.image (fun U : CollisionPadding r ↦ U.val)

omit [DecidableEq G] in
@[simp] theorem mem_collisionPaddingSubsetLayer_iff
    {g : Fin (m + 1) → G} {h : G}
    {r : ReducedSubsetSumCollision g h} {S : Finset (Fin m)} :
    S ∈ collisionPaddingSubsetLayer r ↔
      S ⊆ Finset.univ \ reducedCollisionSupport r := by
  classical
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨U, _, rfl⟩
    simpa [reducedCollisionSupport] using U.property
  · intro hS
    exact Finset.mem_image.mpr
      ⟨⟨S, by simpa [reducedCollisionSupport] using hS⟩,
        Finset.mem_univ _, rfl⟩

omit [DecidableEq G] in
theorem card_collisionPaddingSubsetLayer
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) :
    (collisionPaddingSubsetLayer r).card =
      reducedCollisionWeight (m := m) r := by
  classical
  change (Finset.univ.image
      (fun U : CollisionPadding r ↦ U.val)).card = _
  have hinj : Function.Injective (fun U : CollisionPadding r ↦ U.val) := by
    intro U V hUV
    exact Subtype.ext hUV
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
    card_collisionPadding (g := g) (h := h) r]
  rfl

/-- Group values of the root padding cube. -/
noncomputable def collisionPaddingValueLayer
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) : Finset G :=
  (collisionPaddingSubsetLayer r).image (ssum g)

/-- Validity makes the root padding values distinct. -/
theorem card_collisionPaddingValueLayer
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g h) :
    (collisionPaddingValueLayer r).card =
      reducedCollisionWeight (m := m) r := by
  rw [collisionPaddingValueLayer,
    Finset.card_image_of_injective _ (ssum_injective g hg),
    card_collisionPaddingSubsetLayer]

/-- Ordinary subsets underlying the full restored target layer. -/
noncomputable def restoredCollisionSubsetLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.image
    (restoredCollisionSubset (r := r) (q := q))

omit [DecidableEq G] in
theorem card_restoredCollisionSubsetLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    (restoredCollisionSubsetLayer r q).card =
      reducedCollisionWeight (m := m) r := by
  classical
  rw [restoredCollisionSubsetLayer,
    Finset.card_image_of_injective _
      (restoredCollisionSubset_injective r q hcard),
    Finset.card_univ, card_restoredCollisionPadding r q hcard]

/-- Padding common to both shapes: it lies outside the union of their
supports. -/
def JointCollisionPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :=
  {U : Finset (Fin m) //
    U ⊆ Finset.univ \
      (reducedCollisionSupport r ∪ reducedCollisionSupport q)}

noncomputable instance instFintypeJointCollisionPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    Fintype (JointCollisionPadding r q) := by
  unfold JointCollisionPadding
  infer_instance

omit [DecidableEq G] in
theorem card_jointCollisionPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    Fintype.card (JointCollisionPadding r q) =
      reducedCollisionJointPaddingWeight r q := by
  classical
  change Fintype.card
      {U : Finset (Fin m) // U ⊆ Finset.univ \
        (reducedCollisionSupport r ∪ reducedCollisionSupport q)} =
    2 ^ (m -
      (reducedCollisionSupport r ∪ reducedCollisionSupport q).card)
  rw [Fintype.card_subtype]
  have hfilter :
      Finset.univ.filter (fun U : Finset (Fin m) ↦
          U ⊆ Finset.univ \
            (reducedCollisionSupport r ∪ reducedCollisionSupport q)) =
        (Finset.univ \
          (reducedCollisionSupport r ∪ reducedCollisionSupport q)).powerset := by
    ext U
    simp
  rw [hfilter, Finset.card_powerset, Finset.card_sdiff,
    Finset.inter_univ, Finset.card_univ, Fintype.card_fin]

/-- Objects in the common part of the restored target layer and root padding
cube. -/
def RootCompatibleRestoredPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :=
  CollisionRestorationChoice r q × JointCollisionPadding r q

noncomputable instance instFintypeRootCompatibleRestoredPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    Fintype (RootCompatibleRestoredPadding r q) := by
  unfold RootCompatibleRestoredPadding
  infer_instance

/-- A joint padding is in particular a legal target padding. -/
def jointCollisionPaddingToTargetPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (U : JointCollisionPadding r q) : CollisionPadding q :=
  ⟨U.val, by
    intro k hk
    have hk' := Finset.mem_sdiff.mp (U.property hk)
    exact Finset.mem_sdiff.mpr
      ⟨hk'.1, fun hkq ↦ hk'.2 (Finset.mem_union_right _ hkq)⟩⟩

/-- Embed a root-compatible object into the full restored target layer. -/
def rootCompatibleToRestoredPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (x : RootCompatibleRestoredPadding r q) :
    RestoredCollisionPadding r q :=
  (x.1, jointCollisionPaddingToTargetPadding r q x.2)

/-- Ordinary subset represented by a root-compatible restored object. -/
def rootCompatibleRestoredSubset
    {g : Fin (m + 1) → G} {h : G}
    {r q : ReducedSubsetSumCollision g h}
    (x : RootCompatibleRestoredPadding r q) : Finset (Fin m) :=
  restoredCollisionSubset (rootCompatibleToRestoredPadding r q x)

omit [DecidableEq G] in
theorem rootCompatibleToRestoredPadding_injective
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    Function.Injective (rootCompatibleToRestoredPadding r q) := by
  intro x y hxy
  apply Prod.ext
  · exact congrArg (fun z : RestoredCollisionPadding r q ↦ z.1) hxy
  · apply Subtype.ext
    exact congrArg (fun z : RestoredCollisionPadding r q ↦ z.2.val) hxy

omit [DecidableEq G] in
theorem rootCompatibleRestoredSubset_injective
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    Function.Injective
      (rootCompatibleRestoredSubset (r := r) (q := q)) :=
  (restoredCollisionSubset_injective r q hcard).comp
    (rootCompatibleToRestoredPadding_injective r q)

/-- The common subset layer built from restoration choices and joint
paddings. -/
noncomputable def rootCompatibleRestoredSubsetLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Finset (Fin m)) := by
  classical
  exact Finset.univ.image
    (rootCompatibleRestoredSubset (r := r) (q := q))

omit [DecidableEq G] in
theorem card_rootCompatibleRestoredSubsetLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    (rootCompatibleRestoredSubsetLayer r q).card =
      2 ^ reducedCollisionSupportDepth r q *
        reducedCollisionJointPaddingWeight r q := by
  classical
  rw [rootCompatibleRestoredSubsetLayer,
    Finset.card_image_of_injective _
      (rootCompatibleRestoredSubset_injective r q hcard),
    Finset.card_univ]
  change Fintype.card
      (CollisionRestorationChoice r q × JointCollisionPadding r q) = _
  rw [Fintype.card_prod, card_collisionRestorationChoice r q hcard,
    card_jointCollisionPadding]

omit [DecidableEq G] in
/-- A restored subset is a legal root padding exactly when its target-padding
factor avoids all dropped root support. -/
theorem restoredCollisionSubset_subset_root_compl_iff
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (x : RestoredCollisionPadding r q) :
    restoredCollisionSubset x ⊆
        Finset.univ \ reducedCollisionSupport r ↔
      Disjoint x.2.val (reducedCollisionDroppedSupport r q) := by
  constructor
  · intro hx
    rw [Finset.disjoint_left]
    intro k hkU hkD
    have hkroot := (Finset.mem_sdiff.mp hkD).1
    have hkrestored : k ∈ restoredCollisionSubset x :=
      Finset.mem_union_right _ hkU
    exact (Finset.mem_sdiff.mp (hx hkrestored)).2 hkroot
  · intro hdisj k hk
    have hkUniv : k ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ k
    refine Finset.mem_sdiff.mpr ⟨hkUniv, ?_⟩
    intro hkroot
    rcases Finset.mem_union.mp hk with hkV | hkU
    · have hkext := (restorationSupport_subset_external r q hcard)
        (x.1.property hkV)
      exact (Finset.mem_sdiff.mp hkext).2 hkroot
    · have hknotq : k ∉ reducedCollisionSupport q := fun hkq ↦
        Finset.disjoint_left.mp (collisionPadding_disjoint_support q x.2)
          hkU hkq
      have hkD : k ∈ reducedCollisionDroppedSupport r q :=
        Finset.mem_sdiff.mpr ⟨hkroot, hknotq⟩
      exact Finset.disjoint_left.mp hdisj hkU hkD

omit [DecidableEq G] in
/-- The subset-level intersection is exactly the joint-padding layer. -/
theorem restoredSubsetLayer_inter_rootPaddingLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    restoredCollisionSubsetLayer r q ∩ collisionPaddingSubsetLayer r =
      rootCompatibleRestoredSubsetLayer r q := by
  classical
  ext S
  constructor
  · intro hS
    have hRestored := (Finset.mem_inter.mp hS).1
    have hRoot := (Finset.mem_inter.mp hS).2
    rcases Finset.mem_image.mp hRestored with ⟨x, _, hxS⟩
    have hSroot := mem_collisionPaddingSubsetLayer_iff.mp hRoot
    have hxroot : restoredCollisionSubset x ⊆
        Finset.univ \ reducedCollisionSupport r := by
      simpa [hxS] using hSroot
    have hdisj :=
      (restoredCollisionSubset_subset_root_compl_iff r q hcard x).mp hxroot
    have hUjoint : x.2.val ⊆ Finset.univ \
        (reducedCollisionSupport r ∪ reducedCollisionSupport q) := by
      intro k hkU
      have hkUniv : k ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ k
      refine Finset.mem_sdiff.mpr ⟨hkUniv, ?_⟩
      intro hkUnion
      rcases Finset.mem_union.mp hkUnion with hkR | hkQ
      · have hknotQ : k ∉ reducedCollisionSupport q := fun hkQ' ↦
          Finset.disjoint_left.mp (collisionPadding_disjoint_support q x.2)
            hkU hkQ'
        exact Finset.disjoint_left.mp hdisj hkU
          (Finset.mem_sdiff.mpr ⟨hkR, hknotQ⟩)
      · exact Finset.disjoint_left.mp (collisionPadding_disjoint_support q x.2)
          hkU hkQ
    let y : RootCompatibleRestoredPadding r q :=
      (x.1, ⟨x.2.val, hUjoint⟩)
    have hyS : rootCompatibleRestoredSubset y = S := by
      change x.1.val ∪ x.2.val = S
      change x.1.val ∪ x.2.val = S at hxS
      exact hxS
    exact Finset.mem_image.mpr ⟨y, Finset.mem_univ _, hyS⟩
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨x, _, rfl⟩
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr
        ⟨rootCompatibleToRestoredPadding r q x, Finset.mem_univ _, rfl⟩
    · apply mem_collisionPaddingSubsetLayer_iff.mpr
      intro k hk
      rcases Finset.mem_union.mp hk with hkV | hkU
      · have hkext := (restorationSupport_subset_external r q hcard)
          (x.1.property hkV)
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hkext).2⟩
      · have hkJoint := Finset.mem_sdiff.mp (x.2.property hkU)
        exact Finset.mem_sdiff.mpr
          ⟨hkJoint.1, fun hkR ↦ hkJoint.2 (Finset.mem_union_left _ hkR)⟩

omit [DecidableEq G] in
/-- Exact cardinality of the root/restored subset intersection. -/
theorem card_restoredSubsetLayer_inter_rootPaddingLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    (restoredCollisionSubsetLayer r q ∩
        collisionPaddingSubsetLayer r).card =
      2 ^ reducedCollisionSupportDepth r q *
        reducedCollisionJointPaddingWeight r q := by
  rw [restoredSubsetLayer_inter_rootPaddingLayer r q hcard,
    card_rootCompatibleRestoredSubsetLayer r q hcard]

omit [DecidableEq G] in
/-- Images under an injective map preserve finite intersections. -/
theorem image_inter_eq_image_inter_of_injective
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (hf : Function.Injective f) (A B : Finset α) :
    A.image f ∩ B.image f = (A ∩ B).image f := by
  ext y
  constructor
  · intro hy
    rcases Finset.mem_image.mp (Finset.mem_inter.mp hy).1 with
      ⟨a, ha, hay⟩
    rcases Finset.mem_image.mp (Finset.mem_inter.mp hy).2 with
      ⟨b, hb, hby⟩
    have hab : a = b := hf (hay.trans hby.symm)
    subst b
    exact Finset.mem_image.mpr
      ⟨a, Finset.mem_inter.mpr ⟨ha, hb⟩, hay⟩
  · intro hy
    rcases Finset.mem_image.mp hy with ⟨a, ha, rfl⟩
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨a, (Finset.mem_inter.mp ha).1, rfl⟩,
        Finset.mem_image.mpr ⟨a, (Finset.mem_inter.mp ha).2, rfl⟩⟩

/-- The previously defined restored value layer is the image of its concrete
ordinary-subset layer. -/
theorem restoredCollisionValueLayer_eq_subsetLayer_image
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    restoredCollisionValueLayer r q =
      (restoredCollisionSubsetLayer r q).image (ssum g) := by
  classical
  ext x
  simp [restoredCollisionValueLayer, restoredCollisionSubsetLayer,
    restoredCollisionValue]

/-- Exact cardinality of the root/restored intersection at the group-value
level. -/
theorem card_restoredValueLayer_inter_rootPaddingValueLayer
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    (restoredCollisionValueLayer r q ∩
        collisionPaddingValueLayer r).card =
      2 ^ reducedCollisionSupportDepth r q *
        reducedCollisionJointPaddingWeight r q := by
  rw [restoredCollisionValueLayer_eq_subsetLayer_image,
    collisionPaddingValueLayer,
    image_inter_eq_image_inter_of_injective
      (ssum g) (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg),
    card_restoredSubsetLayer_inter_rootPaddingLayer r q hcard]

/-- A nonempty dropped support makes the root/restored intersection at most
half of a full dominant-weight layer. -/
theorem two_mul_card_restoredValueLayer_inter_root_le
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    2 * (restoredCollisionValueLayer r q ∩
        collisionPaddingValueLayer r).card ≤
      reducedCollisionWeight (m := m) r := by
  have hexact :=
    card_externalSupport_eq_card_droppedSupport_add_depth r q hcard
  have hdropPos : 0 < (reducedCollisionDroppedSupport r q).card :=
    Finset.card_pos.mpr hdrop
  have hdepth : reducedCollisionSupportDepth r q + 1 ≤
      (reducedCollisionExternalSupport r q).card := by omega
  have hpow := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hdepth
  rw [card_restoredValueLayer_inter_rootPaddingValueLayer hg r q hcard,
    reducedCollisionWeight_eq_pow_external_mul_jointPadding r q]
  calc
    2 * (2 ^ reducedCollisionSupportDepth r q *
        reducedCollisionJointPaddingWeight r q) =
      2 ^ (reducedCollisionSupportDepth r q + 1) *
        reducedCollisionJointPaddingWeight r q := by
      rw [pow_succ]
      ring
    _ ≤ 2 ^ (reducedCollisionExternalSupport r q).card *
        reducedCollisionJointPaddingWeight r q :=
      Nat.mul_le_mul_right _ hpow

/-- For every actual strict-majority escape target, the restored layer and
root padding cube overlap in at most half their common full size. -/
theorem canonicalSupportEscapeTarget_two_mul_restored_inter_root_le
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g) (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    {j : Fin m} {q : ReducedSubsetSumCollision g h}
    (hjq : (j, q) ∈ canonicalSupportEscapeIncidences hh r) :
    2 * (restoredCollisionValueLayer r q ∩
        collisionPaddingValueLayer r).card ≤
      reducedCollisionWeight (m := m) r := by
  have hjq' := mem_canonicalSupportEscapeIncidences_iff.mp hjq
  have hqr := reducedCollision_ne_of_right_mem_of_avoids
    r q hjq'.1 hjq'.2.2.1
  have hgrowth := canonical_other_support_growth_of_strictMajority
    hh r hr hmajor q hjq'.2.1 hqr
  have hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card := by
    simpa [reducedCollisionSupport] using hgrowth.1.le
  exact two_mul_card_restoredValueLayer_inter_root_le hg r q hcard
    ⟨j, Finset.mem_sdiff.mpr
    ⟨by simpa [reducedCollisionSupport] using
        Finset.mem_union_right r.val.1 hjq'.1,
      by simpa [reducedCollisionSupport] using hjq'.2.2.1⟩⟩

/-- Equivalently, the union of the root padding values and one actual restored
escape layer has at least three halves of the dominant weight. -/
theorem three_mul_weight_le_two_mul_card_root_union_restored_of_escape
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g) (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    {j : Fin m} {q : ReducedSubsetSumCollision g h}
    (hjq : (j, q) ∈ canonicalSupportEscapeIncidences hh r) :
    3 * reducedCollisionWeight (m := m) r ≤
      2 * (collisionPaddingValueLayer r ∪
        restoredCollisionValueLayer r q).card := by
  have hinter :=
    canonicalSupportEscapeTarget_two_mul_restored_inter_root_le
      hg hh r hr hmajor hjq
  have hinter' : 2 * (collisionPaddingValueLayer r ∩
      restoredCollisionValueLayer r q).card ≤
      reducedCollisionWeight (m := m) r := by
    simpa [Finset.inter_comm] using hinter
  have hqr := reducedCollision_ne_of_right_mem_of_avoids
    r q (mem_canonicalSupportEscapeIncidences_iff.mp hjq).1
      (mem_canonicalSupportEscapeIncidences_iff.mp hjq).2.2.1
  have hgrowth := canonical_other_support_growth_of_strictMajority
    hh r hr hmajor q
      (mem_canonicalSupportEscapeIncidences_iff.mp hjq).2.1 hqr
  have hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card := by
    simpa [reducedCollisionSupport] using hgrowth.1.le
  have hunion := Finset.card_union_add_card_inter
    (collisionPaddingValueLayer r) (restoredCollisionValueLayer r q)
  rw [card_collisionPaddingValueLayer hg r,
    card_restoredCollisionValueLayer hg r q hcard] at hunion
  omega

/-- Package saying that a restored target is quantitatively separated from
the root padding cube. -/
def IsRootSeparatedRestoredLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Prop :=
  2 * (restoredCollisionValueLayer r q ∩
      collisionPaddingValueLayer r).card ≤
    reducedCollisionWeight (m := m) r ∧
  3 * reducedCollisionWeight (m := m) r ≤
    2 * (collisionPaddingValueLayer r ∪
      restoredCollisionValueLayer r q).card

/-- Every target occurring in the strict-majority escape relation is root
separated. -/
theorem canonicalSupportEscapeTarget_isRootSeparatedRestoredLayer
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g) (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    {j : Fin m} {q : ReducedSubsetSumCollision g h}
    (hjq : (j, q) ∈ canonicalSupportEscapeIncidences hh r) :
    IsRootSeparatedRestoredLayer r q :=
  ⟨canonicalSupportEscapeTarget_two_mul_restored_inter_root_le
      hg hh r hr hmajor hjq,
    three_mul_weight_le_two_mul_card_root_union_restored_of_escape
      hg hh r hr hmajor hjq⟩

end MinModulus
