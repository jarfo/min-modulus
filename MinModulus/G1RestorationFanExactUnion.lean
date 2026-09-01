/-
# Exact union of a depth-indexed restoration fan

The second-moment estimate for a restoration fan ignores its common
coordinate structure.  Let `H` be the chosen `(depth+1)`-set of external
coordinates.  For `e in H`, the blocked signature is exactly

`(supp(q) \ H) ∪ {e}`.

Consequently the union of all fan lower layers is the enlarged lower cube
avoiding `supp(q) \ H`, with the subface containing every coordinate of `H`
removed.  The enlarged cube has size `2 w_r`.  The removed subface is in
bijection with the ordinary target paddings via `U ↦ H ∪ U`, so it has
size `w_q`.  The exact fan union therefore has size `2 w_r - w_q`.

In the live two-tail residual, `8 w_q ≤ w_r`; hence this is at least
`15 w_r / 8`.  The whole fan still avoids the negative-tail upper face, so
that complete face can be adjoined without loss.
-/
import MinModulus.G1RestorationFanPacking

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Union of the ordinary lower subset layers indexed by the restoration
fan. -/
noncomputable def restorationFanSubsetUnion
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Finset (Fin m)) := by
  classical
  exact (reducedCollisionRestorationFanSupport r q).biUnion (fun e ↦
    blockedSignatureSubsetLayer (restorationFanBlockedSupport r q e))

omit [DecidableEq G] in
/-- A fan blocked signature is a fixed common block plus its one retained fan
coordinate. -/
theorem restorationFanBlockedSupport_eq_sdiff_union_singleton
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    {e : Fin m}
    (he : e ∈ reducedCollisionRestorationFanSupport r q) :
    restorationFanBlockedSupport r q e =
      (reducedCollisionSupport q \
        reducedCollisionRestorationFanSupport r q) ∪ {e} := by
  have hHext := restorationFanSupport_subset_external r q hcard hdrop
  have heq : e ∈ reducedCollisionSupport q :=
    Finset.sdiff_subset (hHext he)
  ext j
  by_cases hje : j = e
  · subst j
    simp [restorationFanBlockedSupport, he, heq]
  · simp [restorationFanBlockedSupport, hje]

omit [DecidableEq G] in
/-- Membership in the exact fan union: avoid the common block, but fail to
contain the entire restoration fan support. -/
theorem mem_restorationFanSubsetUnion_iff
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    {S : Finset (Fin m)} :
    S ∈ restorationFanSubsetUnion r q ↔
      S ⊆ Finset.univ \ (reducedCollisionSupport q \
        reducedCollisionRestorationFanSupport r q) ∧
      ¬ reducedCollisionRestorationFanSupport r q ⊆ S := by
  classical
  constructor
  · intro hS
    rcases Finset.mem_biUnion.mp hS with ⟨e, he, hSe⟩
    have hSe' := Finset.mem_powerset.mp hSe
    rw [restorationFanBlockedSupport_eq_sdiff_union_singleton
      r q hcard hdrop he] at hSe'
    constructor
    · intro j hjS
      have hjAllowed := hSe' hjS
      have hjNotCommon : j ∉ reducedCollisionSupport q \
          reducedCollisionRestorationFanSupport r q := by
        intro hjCommon
        exact (Finset.mem_sdiff.mp hjAllowed).2
          (Finset.mem_union_left _ hjCommon)
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hjNotCommon⟩
    · intro hHsub
      have heS := hHsub he
      have heAllowed := hSe' heS
      exact (Finset.mem_sdiff.mp heAllowed).2
        (Finset.mem_union_right _ (Finset.mem_singleton_self e))
  · rintro ⟨hScommon, hnotH⟩
    have hexists : ∃ e ∈ reducedCollisionRestorationFanSupport r q,
        e ∉ S := by
      simpa only [Finset.not_subset] using hnotH
    obtain ⟨e, heH, heS⟩ := hexists
    apply Finset.mem_biUnion.mpr
    refine ⟨e, heH, ?_⟩
    rw [blockedSignatureSubsetLayer, Finset.mem_powerset,
      restorationFanBlockedSupport_eq_sdiff_union_singleton
        r q hcard hdrop heH]
    intro j hjS
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hjBlocked
    rcases Finset.mem_union.mp hjBlocked with hjCommon | hje
    · exact (Finset.mem_sdiff.mp (hScommon hjS)).2 hjCommon
    · exact heS (Finset.mem_singleton.mp hje ▸ hjS)

omit [DecidableEq G] in
/-- The exact fan is one enlarged lower cube minus the subface containing all
fan coordinates. -/
theorem restorationFanSubsetUnion_eq_lower_sdiff_upper
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    restorationFanSubsetUnion r q =
      blockedSignatureSubsetLayer (reducedCollisionSupport q \
        reducedCollisionRestorationFanSupport r q) \
      blockedSignatureUpperSubsetLayer
        (reducedCollisionRestorationFanSupport r q) := by
  classical
  ext S
  rw [mem_restorationFanSubsetUnion_iff r q hcard hdrop]
  simp only [Finset.mem_sdiff, blockedSignatureSubsetLayer,
    Finset.mem_powerset, mem_blockedSignatureUpperSubsetLayer_iff]

omit [DecidableEq G] in
/-- The common block has one coordinate fewer than the root support. -/
theorem card_restorationFanCommonBlockedSupport
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    (reducedCollisionSupport q \
      reducedCollisionRestorationFanSupport r q).card =
        (reducedCollisionSupport r).card - 1 := by
  have hHext := restorationFanSupport_subset_external r q hcard hdrop
  have hHq : reducedCollisionRestorationFanSupport r q ⊆
      reducedCollisionSupport q := hHext.trans Finset.sdiff_subset
  rw [Finset.card_sdiff_of_subset hHq,
    card_restorationFanSupport r q hcard hdrop]
  simp only [reducedCollisionSupportDepth]
  omega

omit [DecidableEq G] in
/-- The enlarged lower cube has exactly twice the root padding weight. -/
theorem card_restorationFanEnlargedLowerLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    (blockedSignatureSubsetLayer (reducedCollisionSupport q \
      reducedCollisionRestorationFanSupport r q)).card =
        2 * reducedCollisionWeight (m := m) r := by
  have hrpos : 0 < (reducedCollisionSupport r).card := by
    have hdropSub : reducedCollisionDroppedSupport r q ⊆
        reducedCollisionSupport r := Finset.sdiff_subset
    exact lt_of_lt_of_le (Finset.card_pos.mpr hdrop)
      (Finset.card_mono hdropSub)
  have hrle : (reducedCollisionSupport r).card ≤ m := by
    simpa [reducedCollisionSupport] using
      Finset.card_le_univ (reducedCollisionSupport r)
  rw [card_blockedSignatureSubsetLayer,
    card_restorationFanCommonBlockedSupport r q hcard hdrop]
  change 2 ^ (m - ((reducedCollisionSupport r).card - 1)) =
    2 * 2 ^ (m - (reducedCollisionSupport r).card)
  have hexp : m - ((reducedCollisionSupport r).card - 1) =
      (m - (reducedCollisionSupport r).card) + 1 := by omega
  rw [hexp, pow_succ]
  ring

omit [DecidableEq G] in
/-- Subsets in the excluded face are exactly `H ∪ U` for legal target
paddings `U`. -/
theorem restorationFanExcludedSubsetLayer_eq_padding_image
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    blockedSignatureSubsetLayer (reducedCollisionSupport q \
        reducedCollisionRestorationFanSupport r q) ∩
      blockedSignatureUpperSubsetLayer
        (reducedCollisionRestorationFanSupport r q) =
      Finset.univ.image (fun U : CollisionPadding q ↦
        reducedCollisionRestorationFanSupport r q ∪ U.val) := by
  classical
  let H := reducedCollisionRestorationFanSupport r q
  let Q := reducedCollisionSupport q
  have hHext := restorationFanSupport_subset_external r q hcard hdrop
  have hHQ : H ⊆ Q := hHext.trans Finset.sdiff_subset
  ext S
  constructor
  · intro hS
    have hLower := (Finset.mem_inter.mp hS).1
    have hUpper := (Finset.mem_inter.mp hS).2
    have hAvoid := Finset.mem_powerset.mp hLower
    have hHsub := mem_blockedSignatureUpperSubsetLayer_iff.mp hUpper
    let Uset := S \ H
    have hU : Uset ⊆ Finset.univ \ (q.val.1 ∪ q.val.2) := by
      intro j hjU
      have hj' := Finset.mem_sdiff.mp hjU
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hjq
      have hjQ : j ∈ Q := by simpa [Q, reducedCollisionSupport] using hjq
      have hjQH : j ∈ Q \ H := Finset.mem_sdiff.mpr ⟨hjQ, hj'.2⟩
      exact (Finset.mem_sdiff.mp (hAvoid hj'.1)).2 hjQH
    let U : CollisionPadding q := ⟨Uset, hU⟩
    apply Finset.mem_image.mpr
    refine ⟨U, Finset.mem_univ _, ?_⟩
    change H ∪ (S \ H) = S
    exact Finset.union_sdiff_of_subset hHsub
  · intro hS
    rcases Finset.mem_image.mp hS with ⟨U, _hU, rfl⟩
    apply Finset.mem_inter.mpr
    constructor
    · apply Finset.mem_powerset.mpr
      intro j hj
      apply Finset.mem_sdiff.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      intro hjQH
      have hjQH' := Finset.mem_sdiff.mp hjQH
      rcases Finset.mem_union.mp hj with hjH | hjU
      · exact hjQH'.2 hjH
      · have hjOutside := Finset.mem_sdiff.mp (U.property hjU)
        exact hjOutside.2 (by
          simpa [Q, reducedCollisionSupport] using hjQH'.1)
    · exact mem_blockedSignatureUpperSubsetLayer_iff.mpr
        Finset.subset_union_left

omit [DecidableEq G] in
/-- The excluded fixed-coordinate face has exactly the target's native
padding weight. -/
theorem card_restorationFanExcludedSubsetLayer
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    (blockedSignatureSubsetLayer (reducedCollisionSupport q \
          reducedCollisionRestorationFanSupport r q) ∩
        blockedSignatureUpperSubsetLayer
          (reducedCollisionRestorationFanSupport r q)).card =
      reducedCollisionWeight (m := m) q := by
  classical
  rw [restorationFanExcludedSubsetLayer_eq_padding_image
    r q hcard hdrop]
  have hinj : Function.Injective (fun U : CollisionPadding q ↦
      reducedCollisionRestorationFanSupport r q ∪ U.val) := by
    intro U V hUV
    change reducedCollisionRestorationFanSupport r q ∪ U.val =
      reducedCollisionRestorationFanSupport r q ∪ V.val at hUV
    have hHext := restorationFanSupport_subset_external r q hcard hdrop
    have hHQ : reducedCollisionRestorationFanSupport r q ⊆
        reducedCollisionSupport q := hHext.trans Finset.sdiff_subset
    have hHU : Disjoint (reducedCollisionRestorationFanSupport r q) U.val := by
      rw [Finset.disjoint_left]
      intro j hjH hjU
      exact Finset.disjoint_left.mp (collisionPadding_disjoint_support q U)
        hjU (hHQ hjH)
    have hHV : Disjoint (reducedCollisionRestorationFanSupport r q) V.val := by
      rw [Finset.disjoint_left]
      intro j hjH hjV
      exact Finset.disjoint_left.mp (collisionPadding_disjoint_support q V)
        hjV (hHQ hjH)
    apply Subtype.ext
    calc
      U.val = (reducedCollisionRestorationFanSupport r q ∪ U.val) \
          reducedCollisionRestorationFanSupport r q :=
        (Finset.union_sdiff_cancel_left hHU).symm
      _ = (reducedCollisionRestorationFanSupport r q ∪ V.val) \
          reducedCollisionRestorationFanSupport r q := by rw [hUV]
      _ = V.val := Finset.union_sdiff_cancel_left hHV
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ,
    card_collisionPadding]
  rfl

omit [DecidableEq G] in
/-- Exact subset-level cardinality of the restoration fan. -/
theorem card_restorationFanSubsetUnion
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    (restorationFanSubsetUnion r q).card =
      2 * reducedCollisionWeight (m := m) r -
        reducedCollisionWeight (m := m) q := by
  rw [restorationFanSubsetUnion_eq_lower_sdiff_upper r q hcard hdrop,
    Finset.card_sdiff, Finset.inter_comm,
    card_restorationFanEnlargedLowerLayer r q hcard hdrop,
    card_restorationFanExcludedSubsetLayer r q hcard hdrop]

/-- Subset-sum values carried by the exact restoration fan. -/
noncomputable def restorationFanValueUnion
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset G :=
  (restorationFanSubsetUnion r q).image (ssum g)

/-- Validity transports the exact fan count to group values. -/
theorem card_restorationFanValueUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty) :
    (restorationFanValueUnion r q).card =
      2 * reducedCollisionWeight (m := m) r -
        reducedCollisionWeight (m := m) q := by
  rw [restorationFanValueUnion,
    Finset.card_image_of_injective _ (ssum_injective g hg),
    card_restorationFanSubsetUnion r q hcard hdrop]

/-- Every exact fan value remains in the anchored tail subset-sum cube. -/
theorem restorationFanValueUnion_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    restorationFanValueUnion r q ⊆ subsetSumRange g := by
  classical
  intro x hx
  rw [restorationFanValueUnion] at hx
  rcases Finset.mem_image.mp hx with ⟨S, hS, rfl⟩
  rw [subsetSumRange]
  exact Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩

/-- Factor-eight target loss turns the exact `2w_r-w_q` count into a
`15w_r/8` fan expansion. -/
theorem fifteen_mul_weight_le_eight_mul_card_restorationFanValueUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (heighth : 8 * reducedCollisionWeight (m := m) q ≤
      reducedCollisionWeight (m := m) r) :
    15 * reducedCollisionWeight (m := m) r ≤
      8 * (restorationFanValueUnion r q).card := by
  rw [card_restorationFanValueUnion hg r q hcard hdrop]
  omega

/-- Exact fan value union enlarged by a forced-coordinate upper face. -/
noncomputable def restorationFanValueUnionWithUpper
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (T : Finset (Fin m)) : Finset G :=
  restorationFanValueUnion r q ∪ blockedSignatureUpperValueLayer g T

/-- An upper face meeting the target on root coordinates is disjoint from
the entire exact restoration fan. -/
theorem blockedSignatureUpperValueLayer_disjoint_restorationFanValueUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (T : Finset (Fin m))
    (hTsub : T ⊆ reducedCollisionSupport r)
    (hTtarget : (T ∩ reducedCollisionSupport q).Nonempty) :
    Disjoint (blockedSignatureUpperValueLayer g T)
      (restorationFanValueUnion r q) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxUpper hxFan
  rw [blockedSignatureUpperValueLayer] at hxUpper
  rw [restorationFanValueUnion] at hxFan
  rcases Finset.mem_image.mp hxUpper with ⟨S, hSupper, hSx⟩
  rcases Finset.mem_image.mp hxFan with ⟨U, hUfan, hUx⟩
  have hSU : S = U := ssum_injective g hg (hSx.trans hUx.symm)
  subst U
  rcases Finset.mem_biUnion.mp hUfan with ⟨e, he, hSe⟩
  have hTfan : (T ∩ restorationFanBlockedSupport r q e).Nonempty := by
    rcases hTtarget with ⟨j, hj⟩
    have hjT := (Finset.mem_inter.mp hj).1
    have hjq := (Finset.mem_inter.mp hj).2
    have hjroot : j ∈ reducedCollisionSupport r := hTsub hjT
    exact ⟨j, Finset.mem_inter.mpr ⟨hjT,
      (mem_restorationFanBlockedSupport_iff_of_mem_rootSupport
        r q hcard hdrop e hjroot).2 hjq⟩⟩
  exact Finset.disjoint_left.mp
    (blockedSignatureUpperSubsetLayer_disjoint T
      (restorationFanBlockedSupport r q e) hTfan) hSupper hSe

/-- Exact cardinality after adjoining a disjoint upper face to the fan. -/
theorem card_restorationFanValueUnionWithUpper
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card)
    (hdrop : (reducedCollisionDroppedSupport r q).Nonempty)
    (T : Finset (Fin m))
    (hTsub : T ⊆ reducedCollisionSupport r)
    (hTtarget : (T ∩ reducedCollisionSupport q).Nonempty) :
    (restorationFanValueUnionWithUpper r q T).card =
      (2 * reducedCollisionWeight (m := m) r -
        reducedCollisionWeight (m := m) q) + 2 ^ (m - T.card) := by
  have hdisj :=
    blockedSignatureUpperValueLayer_disjoint_restorationFanValueUnion
      hg r q hcard hdrop T hTsub hTtarget
  rw [restorationFanValueUnionWithUpper,
    Finset.card_union_of_disjoint hdisj.symm,
    card_restorationFanValueUnion hg r q hcard hdrop,
    card_blockedSignatureUpperValueLayer hg T]

/-- The exact fan plus upper face remains inside the anchored cube. -/
theorem restorationFanValueUnionWithUpper_subset_subsetSumRange
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) (T : Finset (Fin m)) :
    restorationFanValueUnionWithUpper r q T ⊆ subsetSumRange g := by
  classical
  intro x hx
  rcases Finset.mem_union.mp hx with hxFan | hxUpper
  · exact restorationFanValueUnion_subset_subsetSumRange r q hxFan
  · rw [blockedSignatureUpperValueLayer] at hxUpper
    rcases Finset.mem_image.mp hxUpper with ⟨S, hS, rfl⟩
    rw [subsetSumRange]
    exact Finset.mem_image.mpr ⟨S, Finset.mem_univ _, rfl⟩

section CriticalExactRestorationFan

/-- The live two-tail residual contains an exact restoration fan of size
`2w_r-w_v`.  Factor-eight target decay makes that fan at least `15w_r/8`,
and the full negative-tail upper face remains disjoint. -/
theorem genuineDominant_two_tail_exists_restorationFan_exact_tailFace_packing
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hBcard : r.val.2.card = 2) :
    ∃ v : ReducedSubsetSumCollision g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
      v ∈ criticalCanonicalReducedCollisions g ∧ v ≠ r ∧
      3 ≤ v.val.2.card ∧
      (reducedCollisionDroppedSupport r v).Nonempty ∧
      3 ≤ reducedCollisionSupportDepth r v ∧
      (reducedCollisionSupport r).card + 3 ≤
        (reducedCollisionSupport v).card ∧
      8 * reducedCollisionWeight (m := n) v ≤
        reducedCollisionWeight (m := n) r ∧
      (restorationFanValueUnion r v).card =
        2 * reducedCollisionWeight (m := n) r -
          reducedCollisionWeight (m := n) v ∧
      15 * reducedCollisionWeight (m := n) r ≤
        8 * (restorationFanValueUnion r v).card ∧
      (restorationFanValueUnionWithUpper r v r.val.2).card =
        (2 * reducedCollisionWeight (m := n) r -
          reducedCollisionWeight (m := n) v) + 2 ^ (n - 2) ∧
      15 * reducedCollisionWeight (m := n) r + 8 * 2 ^ (n - 2) ≤
        8 * (restorationFanValueUnionWithUpper r v r.val.2).card ∧
      restorationFanValueUnionWithUpper r v r.val.2 ⊆
        subsetSumRange g ∧
      15 * reducedCollisionWeight (m := n) r + 8 * 2 ^ (n - 2) ≤
        8 * 2 ^ n := by
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
  obtain ⟨v, hv, hvr, hvB, hdrop, hdepth, hplus, heighth⟩ :=
    genuineDominant_two_tail_exists_dropped_eighthWeight_growth
      hqodd g hg r hr hres hBcard
  have hr' : r ∈ canonicalReducedCollisions (g := g) hh := by
    simpa [hh, criticalCanonicalReducedCollisions] using hr
  have hvcritical : v ∈ criticalCanonicalReducedCollisions g := by
    simpa [hh, criticalCanonicalReducedCollisions] using hv
  have hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport v).card := by omega
  have hBsub : r.val.2 ⊆ reducedCollisionSupport r := by
    intro j hj
    exact Finset.mem_union_right _ hj
  have hBtarget : (r.val.2 ∩ reducedCollisionSupport v).Nonempty := by
    have hinter := canonicalReducedCollision_negative_tails_inter
      g hg hh (half_ne_zero hN hM) r v
        (mem_canonicalReducedCollisions_iff.mp hr')
        (mem_canonicalReducedCollisions_iff.mp hv)
    rcases hinter with ⟨j, hj⟩
    exact ⟨j, Finset.mem_inter.mpr
      ⟨(Finset.mem_inter.mp hj).1,
        Finset.mem_union_right _ (Finset.mem_inter.mp hj).2⟩⟩
  have hfanCard := card_restorationFanValueUnion
    hg r v hcard hdrop
  have hfan15 :=
    fifteen_mul_weight_le_eight_mul_card_restorationFanValueUnion
      hg r v hcard hdrop heighth
  have hfullCard := card_restorationFanValueUnionWithUpper
    hg r v hcard hdrop r.val.2 hBsub hBtarget
  rw [hBcard] at hfullCard
  have hfull15 :
      15 * reducedCollisionWeight (m := n) r + 8 * 2 ^ (n - 2) ≤
        8 * (restorationFanValueUnionWithUpper r v r.val.2).card := by
    rw [hfullCard]
    omega
  have hsubset :=
    restorationFanValueUnionWithUpper_subset_subsetSumRange r v r.val.2
  have hUle :
      (restorationFanValueUnionWithUpper r v r.val.2).card ≤ 2 ^ n := by
    calc
      (restorationFanValueUnionWithUpper r v r.val.2).card ≤
          (subsetSumRange g).card := Finset.card_le_card hsubset
      _ = 2 ^ n := card_subsetSumRange g hg
  have hambient :
      15 * reducedCollisionWeight (m := n) r + 8 * 2 ^ (n - 2) ≤
        8 * 2 ^ n :=
    hfull15.trans (Nat.mul_le_mul_left 8 hUle)
  exact ⟨v, hvcritical, hvr, hvB, hdrop, hdepth, hplus, heighth,
    hfanCard, hfan15, hfullCard, hfull15, hsubset, hambient⟩

end CriticalExactRestorationFan

end MinModulus
