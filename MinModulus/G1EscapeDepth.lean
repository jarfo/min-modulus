/-
# Exact depth and padding normalization for dominant escapes

The strict-majority branch previously recorded only a factor-two loss when a
canonical target grows support.  Here that loss is made exact.  If the target
support grows by `d`, then its padding weight is exactly `2^d` times smaller.
Equivalently, restoring those `d` binary dimensions normalizes every target
back to the dominant collision's full padding weight.

The same depth is the exact excess of external target coordinates over
dropped source coordinates.  After summing the exact escape fibers, this
gives an aggregate depth tax: source-tail coverage plus the sum of all target
depths is bounded by the total external-support mass.  This is the numerical
input needed to construct disjoint padded escape layers.
-/
import MinModulus.G1MajoritySupportBound

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The reduced tail support of a collision. -/
def reducedCollisionSupport {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) : Finset (Fin m) :=
  r.val.1 ∪ r.val.2

/-- Net support growth from `r` to `q`. -/
def reducedCollisionSupportDepth {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : ℕ :=
  (reducedCollisionSupport q).card - (reducedCollisionSupport r).card

/-- Coordinates dropped when passing from the source support to the target. -/
def reducedCollisionDroppedSupport {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Fin m) :=
  reducedCollisionSupport r \ reducedCollisionSupport q

/-- Coordinates introduced outside the source support by the target. -/
def reducedCollisionExternalSupport {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : Finset (Fin m) :=
  reducedCollisionSupport q \ reducedCollisionSupport r

/-- Padding coordinates common to both reduced shapes. -/
def reducedCollisionJointPaddingWeight {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) : ℕ :=
  2 ^ (m - (reducedCollisionSupport r ∪ reducedCollisionSupport q).card)

omit [DecidableEq G] in
/-- Support growth is exactly external support minus dropped support. -/
theorem card_externalSupport_eq_card_droppedSupport_add_depth
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    (reducedCollisionExternalSupport r q).card =
      (reducedCollisionDroppedSupport r q).card +
        reducedCollisionSupportDepth r q := by
  have hr := Finset.card_sdiff_add_card_inter
    (reducedCollisionSupport r) (reducedCollisionSupport q)
  have hq := Finset.card_sdiff_add_card_inter
    (reducedCollisionSupport q) (reducedCollisionSupport r)
  rw [Finset.inter_comm (reducedCollisionSupport q)
    (reducedCollisionSupport r)] at hq
  simp only [reducedCollisionExternalSupport, reducedCollisionDroppedSupport,
    reducedCollisionSupportDepth]
  omega

omit [DecidableEq G] in
/-- A support increase of depth `d` loses exactly `d` binary padding
dimensions. -/
theorem reducedCollisionWeight_eq_pow_depth_mul
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card) :
    reducedCollisionWeight (m := m) r =
      2 ^ reducedCollisionSupportDepth r q *
        reducedCollisionWeight (m := m) q := by
  have hrle : (reducedCollisionSupport r).card ≤ m := by
    simpa [reducedCollisionSupport] using
      Finset.card_le_univ (reducedCollisionSupport r)
  have hqle : (reducedCollisionSupport q).card ≤ m := by
    simpa [reducedCollisionSupport] using
      Finset.card_le_univ (reducedCollisionSupport q)
  have hexp : m - (reducedCollisionSupport r).card =
      reducedCollisionSupportDepth r q +
        (m - (reducedCollisionSupport q).card) := by
    simp only [reducedCollisionSupportDepth]
    omega
  change 2 ^ (m - (reducedCollisionSupport r).card) =
    2 ^ reducedCollisionSupportDepth r q *
      2 ^ (m - (reducedCollisionSupport q).card)
  rw [hexp, pow_add]

omit [DecidableEq G] in
/-- The source weight splits into choices on the target's external support
and padding common to both shapes. -/
theorem reducedCollisionWeight_eq_pow_external_mul_jointPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    reducedCollisionWeight (m := m) r =
      2 ^ (reducedCollisionExternalSupport r q).card *
        reducedCollisionJointPaddingWeight r q := by
  have hunion :
      (reducedCollisionExternalSupport r q).card +
          (reducedCollisionSupport r).card =
        (reducedCollisionSupport r ∪ reducedCollisionSupport q).card := by
    have h := Finset.card_sdiff_add_card
      (reducedCollisionSupport q) (reducedCollisionSupport r)
    simpa [reducedCollisionExternalSupport, Finset.union_comm] using h
  have huniv :
      (reducedCollisionSupport r ∪ reducedCollisionSupport q).card ≤ m := by
    simpa [reducedCollisionSupport] using
      Finset.card_le_univ
        (reducedCollisionSupport r ∪ reducedCollisionSupport q)
  have hexp : m - (reducedCollisionSupport r).card =
      (reducedCollisionExternalSupport r q).card +
        (m - (reducedCollisionSupport r ∪
          reducedCollisionSupport q).card) := by
    omega
  change 2 ^ (m - (reducedCollisionSupport r).card) =
    2 ^ (reducedCollisionExternalSupport r q).card *
      2 ^ (m - (reducedCollisionSupport r ∪
        reducedCollisionSupport q).card)
  rw [hexp, pow_add]

omit [DecidableEq G] in
/-- Dually, the target weight splits into choices on the source coordinates
it dropped and padding common to both shapes. -/
theorem reducedCollisionWeight_eq_pow_dropped_mul_jointPadding
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h) :
    reducedCollisionWeight (m := m) q =
      2 ^ (reducedCollisionDroppedSupport r q).card *
        reducedCollisionJointPaddingWeight r q := by
  have hunion :
      (reducedCollisionDroppedSupport r q).card +
          (reducedCollisionSupport q).card =
        (reducedCollisionSupport r ∪ reducedCollisionSupport q).card := by
    have h := Finset.card_sdiff_add_card
      (reducedCollisionSupport r) (reducedCollisionSupport q)
    simpa [reducedCollisionDroppedSupport] using h
  have huniv :
      (reducedCollisionSupport r ∪ reducedCollisionSupport q).card ≤ m := by
    simpa [reducedCollisionSupport] using
      Finset.card_le_univ
        (reducedCollisionSupport r ∪ reducedCollisionSupport q)
  have hexp : m - (reducedCollisionSupport q).card =
      (reducedCollisionDroppedSupport r q).card +
        (m - (reducedCollisionSupport r ∪
          reducedCollisionSupport q).card) := by
    omega
  change 2 ^ (m - (reducedCollisionSupport q).card) =
    2 ^ (reducedCollisionDroppedSupport r q).card *
      2 ^ (m - (reducedCollisionSupport r ∪
        reducedCollisionSupport q).card)
  rw [hexp, pow_add]

/-- Exact normalization of every non-dominant target: after restoring its
support depth, it has the dominant collision's full padding weight. -/
theorem canonical_other_exact_depth_of_strictMajority
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    ∀ q ∈ canonicalReducedCollisions (g := g) hh, q ≠ r →
      0 < reducedCollisionSupportDepth r q ∧
      reducedCollisionWeight (m := m) r =
        2 ^ reducedCollisionSupportDepth r q *
          reducedCollisionWeight (m := m) q ∧
      (reducedCollisionExternalSupport r q).card =
        (reducedCollisionDroppedSupport r q).card +
          reducedCollisionSupportDepth r q := by
  intro q hq hqr
  have hgrowth := canonical_other_support_growth_of_strictMajority
    hh r hr hmajor q hq hqr
  have hle : (reducedCollisionSupport r).card ≤
      (reducedCollisionSupport q).card := by
    simpa [reducedCollisionSupport] using hgrowth.1.le
  refine ⟨?_, reducedCollisionWeight_eq_pow_depth_mul r q hle,
    card_externalSupport_eq_card_droppedSupport_add_depth r q hle⟩
  simp only [reducedCollisionSupportDepth]
  simpa [reducedCollisionSupport] using
    Nat.sub_pos_of_lt hgrowth.1

/-- Every actual escape fiber pays its exact support depth in additional
external coordinates. -/
theorem canonicalSupportEscapeTarget_fiber_add_depth_le_external
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    {j : Fin m} {q : ReducedSubsetSumCollision g h}
    (hjq : (j, q) ∈ canonicalSupportEscapeIncidences hh r) :
    (canonicalSupportEscapeTargetFiber r q).card +
        reducedCollisionSupportDepth r q ≤
      (reducedCollisionExternalSupport r q).card := by
  have hjq' := mem_canonicalSupportEscapeIncidences_iff.mp hjq
  have hqr := reducedCollision_ne_of_right_mem_of_avoids
    r q hjq'.1 hjq'.2.2.1
  have hexact := canonical_other_exact_depth_of_strictMajority
    hh r hr hmajor q hjq'.2.1 hqr
  have hfiber : canonicalSupportEscapeTargetFiber r q ⊆
      reducedCollisionDroppedSupport r q := by
    intro k hk
    have hk' := mem_canonicalSupportEscapeTargetFiber_iff.mp hk
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_right _ hk'.1, hk'.2.1⟩
  calc
    (canonicalSupportEscapeTargetFiber r q).card +
        reducedCollisionSupportDepth r q ≤
      (reducedCollisionDroppedSupport r q).card +
        reducedCollisionSupportDepth r q :=
      Nat.add_le_add_right (Finset.card_mono hfiber) _
    _ = (reducedCollisionExternalSupport r q).card := hexact.2.2.symm

/-- Summed escape-depth tax.  Covering the dominant negative tail consumes
external support once for the covered source fibers and once again for every
unit of strict support growth. -/
theorem card_add_sum_supportDepth_le_sum_externalSupport_of_strictMajority
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    (hcover : r.val.2.card ≤
      (canonicalSupportEscapeIncidences hh r).card) :
    r.val.2.card +
        (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionSupportDepth r) ≤
      (canonicalReducedCollisions (g := g) hh).sum (fun q ↦
        (reducedCollisionExternalSupport r q).card) := by
  classical
  let C := canonicalReducedCollisions (g := g) hh
  let fiberWeight : ReducedSubsetSumCollision g h → ℕ := fun q ↦
    (canonicalSupportEscapeTargetFiber r q).card
  have hpoint : ∀ q ∈ C,
      fiberWeight q + reducedCollisionSupportDepth r q ≤
        (reducedCollisionExternalSupport r q).card := by
    intro q hq
    by_cases hqr : q = r
    · subst q
      simp [fiberWeight, canonicalSupportEscapeTargetFiber,
        reducedCollisionSupportDepth, reducedCollisionExternalSupport,
        reducedCollisionSupport]
    · have hexact := canonical_other_exact_depth_of_strictMajority
        hh r hr hmajor q hq hqr
      have hfiber : canonicalSupportEscapeTargetFiber r q ⊆
          reducedCollisionDroppedSupport r q := by
        intro k hk
        have hk' := mem_canonicalSupportEscapeTargetFiber_iff.mp hk
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_union_right _ hk'.1, hk'.2.1⟩
      simp only [fiberWeight]
      calc
        (canonicalSupportEscapeTargetFiber r q).card +
            reducedCollisionSupportDepth r q ≤
          (reducedCollisionDroppedSupport r q).card +
            reducedCollisionSupportDepth r q :=
          Nat.add_le_add_right (Finset.card_mono hfiber) _
        _ = (reducedCollisionExternalSupport r q).card := hexact.2.2.symm
  have hsum : C.sum (fun q ↦
      fiberWeight q + reducedCollisionSupportDepth r q) ≤
      C.sum (fun q ↦ (reducedCollisionExternalSupport r q).card) :=
    Finset.sum_le_sum hpoint
  have hincidence :
      (canonicalSupportEscapeIncidences hh r).card = C.sum fiberWeight := by
    simpa [C, fiberWeight] using
      card_canonicalSupportEscapeIncidences_eq_sum_targetFibers hh r
  calc
    r.val.2.card + C.sum (reducedCollisionSupportDepth r) ≤
        C.sum fiberWeight + C.sum (reducedCollisionSupportDepth r) :=
      Nat.add_le_add_right (hcover.trans_eq hincidence) _
    _ = C.sum (fun q ↦
        fiberWeight q + reducedCollisionSupportDepth r q) := by
      rw [Finset.sum_add_distrib]
    _ ≤ C.sum (fun q ↦
        (reducedCollisionExternalSupport r q).card) := hsum

/-- All canonical targets other than the distinguished root. -/
noncomputable def canonicalOtherReducedCollisions
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) :
    Finset (ReducedSubsetSumCollision g h) := by
  classical
  exact (canonicalReducedCollisions (g := g) hh).erase r

/-- Restoring each non-root target's lost dimensions produces one full
dominant-weight layer per target. -/
theorem sum_other_pow_depth_mul_weight_eq_card_mul_dominantWeight
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    (canonicalOtherReducedCollisions hh r).sum (fun q ↦
        2 ^ reducedCollisionSupportDepth r q *
          reducedCollisionWeight (m := m) q) =
      (canonicalOtherReducedCollisions hh r).card *
        reducedCollisionWeight (m := m) r := by
  classical
  calc
    (canonicalOtherReducedCollisions hh r).sum (fun q ↦
        2 ^ reducedCollisionSupportDepth r q *
          reducedCollisionWeight (m := m) q) =
      (canonicalOtherReducedCollisions hh r).sum (fun _ ↦
        reducedCollisionWeight (m := m) r) := by
        apply Finset.sum_congr rfl
        intro q hq
        have hq' : q ≠ r ∧
            q ∈ canonicalReducedCollisions (g := g) hh := by
          simpa [canonicalOtherReducedCollisions] using hq
        exact (canonical_other_exact_depth_of_strictMajority
          hh r hr hmajor q hq'.2 hq'.1).2.1.symm
    _ = (canonicalOtherReducedCollisions hh r).card *
        reducedCollisionWeight (m := m) r := by simp

end MinModulus
