/-
# Pairwise geometry of restored escape layers

A restored target layer has a simpler intrinsic description than its product
construction suggests.  If `K_q` is the selected restoration support, its
ordinary subsets are exactly the powerset of

`Allowed_q = K_q ∪ (univ \ supp(q))`.

Equivalently, it is the coordinate subcube obtained by forbidding the blocked
set `supp(q) \ K_q`.  Exact depth normalization says every blocked set has
the same cardinality as the dominant root support, and hence every allowed
set has the same cardinality as the root padding complement.

Pairwise intersections are therefore exact coordinate-subcube intersections.
Two distinct allowed (equivalently blocked) signatures overlap in at most
half of one full restored layer, and their union has at least three halves of
the dominant weight.  The only remaining pairwise obstruction is a cluster
of distinct targets with the same blocked-support signature.
-/
import MinModulus.G1RestoredIntersections

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Coordinates that may occur in a restored target subset. -/
noncomputable def restoredCollisionAllowedSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Fin m) :=
  reducedCollisionRestorationSupport r q ∪
    (Finset.univ \ reducedCollisionSupport q)

/-- Coordinates forbidden from a restored target subset. -/
noncomputable def restoredCollisionBlockedSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Fin m) :=
  reducedCollisionSupport q \ reducedCollisionRestorationSupport r q

omit [DecidableEq G] in
/-- The product construction of a restored layer is exactly the powerset of
its allowed-coordinate signature. -/
theorem restoredCollisionSubsetLayer_eq_powerset_allowed
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (_hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    restoredCollisionSubsetLayer r q =
      (restoredCollisionAllowedSupport r q).powerset := by
  classical
  ext S
  constructor
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨x, _, rfl⟩
    apply Finset.mem_powerset.mpr
    intro k hk
    rcases Finset.mem_union.mp hk with hkV | hkU
    · exact Finset.mem_union_left _ (x.1.property hkV)
    · have hkU' := Finset.mem_sdiff.mp (x.2.property hkU)
      exact Finset.mem_union_right _ <| Finset.mem_sdiff.mpr
        ⟨hkU'.1, fun hkQ ↦ hkU'.2 (by
          simpa [reducedCollisionSupport] using hkQ)⟩
  · intro hS
    have hS' := Finset.mem_powerset.mp hS
    let Q := reducedCollisionSupport q
    let V : Finset (Fin m) := S ∩ Q
    let U : Finset (Fin m) := S \ Q
    have hV : V ⊆ reducedCollisionRestorationSupport r q := by
      intro k hk
      have hkS := (Finset.mem_inter.mp hk).1
      have hkQ := (Finset.mem_inter.mp hk).2
      have hkAllowed := hS' hkS
      rcases Finset.mem_union.mp hkAllowed with hkK | hkOutside
      · exact hkK
      · exact False.elim ((Finset.mem_sdiff.mp hkOutside).2 hkQ)
    have hU : U ⊆ Finset.univ \
        (q.val.1 ∪ q.val.2) := by
      intro k hk
      have hk' := Finset.mem_sdiff.mp hk
      exact Finset.mem_sdiff.mpr
        ⟨Finset.mem_univ _, fun hkq ↦ hk'.2 (by
          simpa [Q, reducedCollisionSupport] using hkq)⟩
    let x : RestoredCollisionPadding r q :=
      (⟨V, hV⟩, ⟨U, hU⟩)
    apply Finset.mem_image.mpr
    refine ⟨x, Finset.mem_univ _, ?_⟩
    change V ∪ U = S
    dsimp [V, U]
    rw [Finset.union_comm, Finset.sdiff_union_inter]

omit [DecidableEq G] in
/-- The allowed signature is the complement of the blocked signature. -/
theorem allowedSupport_eq_compl_blockedSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    restoredCollisionAllowedSupport r q =
      Finset.univ \ restoredCollisionBlockedSupport r q := by
  classical
  have hKQ : reducedCollisionRestorationSupport r q ⊆
      reducedCollisionSupport q :=
    (restorationSupport_subset_external r q hcard).trans Finset.sdiff_subset
  ext k
  by_cases hkK : k ∈ reducedCollisionRestorationSupport r q
  · have hkQ := hKQ hkK
    simp [restoredCollisionAllowedSupport, restoredCollisionBlockedSupport,
      hkK, hkQ]
  · by_cases hkQ : k ∈ reducedCollisionSupport q
    · simp [restoredCollisionAllowedSupport, restoredCollisionBlockedSupport,
        hkK, hkQ]
    · simp [restoredCollisionAllowedSupport, restoredCollisionBlockedSupport,
        hkK, hkQ]

omit [DecidableEq G] in
/-- Removing the selected `d` restoration coordinates leaves a blocked set
with exactly the root support cardinality. -/
theorem card_restoredCollisionBlockedSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    (restoredCollisionBlockedSupport r q).card =
      (reducedCollisionSupport r).card := by
  have hKQ : reducedCollisionRestorationSupport r q ⊆
      reducedCollisionSupport q :=
    (restorationSupport_subset_external r q hcard).trans Finset.sdiff_subset
  rw [restoredCollisionBlockedSupport,
    Finset.card_sdiff_of_subset hKQ, card_restorationSupport r q hcard]
  simp only [reducedCollisionSupportDepth]
  omega

omit [DecidableEq G] in
/-- Every restored layer has the same coordinate dimension as the root
padding cube. -/
theorem card_restoredCollisionAllowedSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    (restoredCollisionAllowedSupport r q).card =
      m - (reducedCollisionSupport r).card := by
  have hlayer := card_restoredCollisionSubsetLayer r q hcard
  rw [restoredCollisionSubsetLayer_eq_powerset_allowed r q hcard,
    Finset.card_powerset] at hlayer
  change 2 ^ (restoredCollisionAllowedSupport r q).card =
    2 ^ (m - (reducedCollisionSupport r).card) at hlayer
  exact Nat.pow_right_injective (by norm_num : 1 < (2 : ℕ)) hlayer

omit [DecidableEq G] in
/-- Equality of allowed signatures is equivalent to equality of blocked
signatures. -/
theorem allowedSupport_eq_iff_blockedSupport_eq
    {g : Fin (m + 1) → G} {h : G}
    (r q u : ReducedSubsetSumCollision g h)
    (hqcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hucard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card) :
    restoredCollisionAllowedSupport r q =
        restoredCollisionAllowedSupport r u ↔
      restoredCollisionBlockedSupport r q =
        restoredCollisionBlockedSupport r u := by
  rw [allowedSupport_eq_compl_blockedSupport r q hqcard,
    allowedSupport_eq_compl_blockedSupport r u hucard]
  constructor
  · intro h
    apply Finset.ext
    intro k
    have hk := Finset.ext_iff.mp h k
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hk
    tauto
  · intro h
    rw [h]

omit [DecidableEq G] in
/-- Pairwise restored subset intersections are exact coordinate-subcube
intersections. -/
theorem restoredSubsetLayers_inter_eq_powerset_allowed_inter
    {g : Fin (m + 1) → G} {h : G}
    (r q u : ReducedSubsetSumCollision g h)
    (hqcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hucard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card) :
    restoredCollisionSubsetLayer r q ∩ restoredCollisionSubsetLayer r u =
      (restoredCollisionAllowedSupport r q ∩
        restoredCollisionAllowedSupport r u).powerset := by
  rw [restoredCollisionSubsetLayer_eq_powerset_allowed r q hqcard,
    restoredCollisionSubsetLayer_eq_powerset_allowed r u hucard]
  ext S
  constructor
  · intro hS
    have hSq := Finset.mem_powerset.mp (Finset.mem_inter.mp hS).1
    have hSu := Finset.mem_powerset.mp (Finset.mem_inter.mp hS).2
    exact Finset.mem_powerset.mpr fun k hk ↦
      Finset.mem_inter.mpr ⟨hSq hk, hSu hk⟩
  · intro hS
    have hS' := Finset.mem_powerset.mp hS
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_powerset.mpr fun k hk ↦
          (Finset.mem_inter.mp (hS' hk)).1,
        Finset.mem_powerset.mpr fun k hk ↦
          (Finset.mem_inter.mp (hS' hk)).2⟩

/-- Exact pairwise intersection size at the group-value level. -/
theorem card_restoredValueLayers_inter
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q u : ReducedSubsetSumCollision g h)
    (hqcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hucard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card) :
    (restoredCollisionValueLayer r q ∩
        restoredCollisionValueLayer r u).card =
      2 ^ (restoredCollisionAllowedSupport r q ∩
        restoredCollisionAllowedSupport r u).card := by
  rw [restoredCollisionValueLayer_eq_subsetLayer_image,
    restoredCollisionValueLayer_eq_subsetLayer_image,
    image_inter_eq_image_inter_of_injective
      (ssum g) (ssum_injective g hg),
    Finset.card_image_of_injective _ (ssum_injective g hg),
    restoredSubsetLayers_inter_eq_powerset_allowed_inter
      r q u hqcard hucard,
    Finset.card_powerset]

omit [DecidableEq G] in
/-- Two distinct allowed signatures have intersection dimension at least one
below their common full dimension. -/
theorem card_allowed_inter_add_one_le_of_ne
    {g : Fin (m + 1) → G} {h : G}
    (r q u : ReducedSubsetSumCollision g h)
    (hqcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hucard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hne : restoredCollisionAllowedSupport r q ≠
      restoredCollisionAllowedSupport r u) :
    (restoredCollisionAllowedSupport r q ∩
        restoredCollisionAllowedSupport r u).card + 1 ≤
      (restoredCollisionAllowedSupport r q).card := by
  let A := restoredCollisionAllowedSupport r q
  let B := restoredCollisionAllowedSupport r u
  have hcards : A.card = B.card := by
    rw [card_restoredCollisionAllowedSupport r q hqcard,
      card_restoredCollisionAllowedSupport r u hucard]
  have hproper : (A ∩ B).card ≠ A.card := by
    intro heq
    have hinterA : A ∩ B = A :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_left (by omega)
    have hAB : A ⊆ B := by
      rw [← hinterA]
      exact Finset.inter_subset_right
    have : A = B := Finset.eq_of_subset_of_card_le hAB (by omega)
    exact hne this
  have hle : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
  have hlt : (A ∩ B).card < A.card := lt_of_le_of_ne hle hproper
  simpa [A, B] using hlt

/-- Distinct restored signatures overlap in at most half of one full
dominant-weight layer. -/
theorem two_mul_card_restoredValueLayers_inter_le_of_allowed_ne
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q u : ReducedSubsetSumCollision g h)
    (hqcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hucard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hne : restoredCollisionAllowedSupport r q ≠
      restoredCollisionAllowedSupport r u) :
    2 * (restoredCollisionValueLayer r q ∩
        restoredCollisionValueLayer r u).card ≤
      reducedCollisionWeight (m := m) r := by
  have hdim := card_allowed_inter_add_one_le_of_ne
    r q u hqcard hucard hne
  have hpow := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hdim
  rw [card_restoredValueLayers_inter hg r q u hqcard hucard]
  have hallowed := card_restoredCollisionAllowedSupport r q hqcard
  change 2 * 2 ^ (restoredCollisionAllowedSupport r q ∩
      restoredCollisionAllowedSupport r u).card ≤
    2 ^ (m - (reducedCollisionSupport r).card)
  rw [← hallowed]
  simpa [pow_succ, Nat.mul_comm] using hpow

/-- Distinct restored signatures have a three-halves union, just as one
actual escape target does with the root layer. -/
theorem three_mul_weight_le_two_mul_card_restored_union_of_allowed_ne
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q u : ReducedSubsetSumCollision g h)
    (hqcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hucard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card)
    (hne : restoredCollisionAllowedSupport r q ≠
      restoredCollisionAllowedSupport r u) :
    3 * reducedCollisionWeight (m := m) r ≤
      2 * (restoredCollisionValueLayer r q ∪
        restoredCollisionValueLayer r u).card := by
  have hinter := two_mul_card_restoredValueLayers_inter_le_of_allowed_ne
    hg r q u hqcard hucard hne
  have hunion := Finset.card_union_add_card_inter
    (restoredCollisionValueLayer r q) (restoredCollisionValueLayer r u)
  rw [card_restoredCollisionValueLayer hg r q hqcard,
    card_restoredCollisionValueLayer hg r u hucard] at hunion
  omega

/-- The complete pairwise dichotomy: equal blocked signatures are the only
way two restored target layers can avoid the half-intersection bound. -/
theorem blockedSupport_eq_or_two_mul_restored_inter_le
    {g : Fin (m + 1) → G} {h : G} (hg : ValidTuple g)
    (r q u : ReducedSubsetSumCollision g h)
    (hqcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hucard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport u).card) :
    restoredCollisionBlockedSupport r q =
        restoredCollisionBlockedSupport r u ∨
      2 * (restoredCollisionValueLayer r q ∩
          restoredCollisionValueLayer r u).card ≤
        reducedCollisionWeight (m := m) r := by
  by_cases hblocked : restoredCollisionBlockedSupport r q =
      restoredCollisionBlockedSupport r u
  · exact Or.inl hblocked
  · exact Or.inr <|
      two_mul_card_restoredValueLayers_inter_le_of_allowed_ne
        hg r q u hqcard hucard
          (mt (allowedSupport_eq_iff_blockedSupport_eq
            r q u hqcard hucard).mp hblocked)

end MinModulus
