/-
# Imbalance descent for light canonical transitions

The light-attachment reduction produces another canonical reduced collision,
but a priori this could look like an uncontrolled finite dynamics.  Comparing
the attachment with the old collision witness supplies a monotone quantity.

For a cardinality-oriented reduced collision write its imbalance as
`|B| - |A|`.  A positive-sign light transition either crosses from the old
positive tail into the new negative tail, or lowers this imbalance by at least
two.  A negative-sign transition can only land at imbalance zero or one,
because negating a more unbalanced collision would violate the witness floor
at the anchor.  The strict-drop relation is well founded, so the only
recurrent light behavior left to count is cross-tail or near-balanced.
-/
import MinModulus.G1LightWitnessReduction

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Cardinality imbalance of a reduced collision.  On a canonical collision
this is exactly `|B| - |A|`, without truncation. -/
def reducedCollisionImbalance {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h) : ℕ :=
  r.val.2.card - r.val.1.card

omit [DecidableEq G] in
theorem reducedCollisionImbalance_cast
    {g : Fin (m + 1) → G} {h : G}
    (r : ReducedSubsetSumCollision g h)
    (hcard : r.val.1.card ≤ r.val.2.card) :
    (reducedCollisionImbalance r : ℤ) =
      (r.val.2.card : ℤ) - (r.val.1.card : ℤ) := by
  rw [reducedCollisionImbalance, Nat.cast_sub hcard]

omit [DecidableEq G] in
/-- If a light attachment is represented with positive sign by `q`, validity
forces either a genuine old-positive/new-negative crossing or a drop of at
least two in cardinality imbalance. -/
theorem positive_lightTransition_cross_or_imbalance_drop
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G} (hh0 : h ≠ 0)
    (r q : ReducedSubsetSumCollision g h)
    (hrcard : r.val.1.card ≤ r.val.2.card)
    (hqcard : q.val.1.card ≤ q.val.2.card)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    {j : Fin m} (hj : j ∈ r.val.2) (hcj : c j.succ = 0)
    (hcoeff : subsetCollisionCoeffs q.val.1 q.val.2 = c) :
    (r.val.1 ∩ q.val.2).Nonempty ∨
      reducedCollisionImbalance q + 2 ≤ reducedCollisionImbalance r := by
  rcases attachedWitness_omits_left_or_anchor_deficit
      g hg hh0 r hrcard hc hj hcj with hdeficit | ⟨a, ha, hca⟩
  · right
    have hcoeff0 := congrFun hcoeff 0
    simp only [subsetCollisionCoeffs, Fin.cons_zero] at hcoeff0
    have hrz := reducedCollisionImbalance_cast r hrcard
    have hqz := reducedCollisionImbalance_cast q hqcard
    omega
  · left
    refine ⟨a, Finset.mem_inter.mpr ⟨ha, ?_⟩⟩
    have hqneg : subsetCollisionCoeffs q.val.1 q.val.2 a.succ = -1 := by
      rw [hcoeff, hca]
    exact (Finset.mem_sdiff.mp
      ((subsetCollisionCoeffs_tail_eq_neg_one_iff_mem_sdiff
        q.val.1 q.val.2 a).mp hqneg)).1

omit [DecidableEq G] in
/-- A negative-sign light transition can only point to a balanced or
minimally unbalanced canonical collision. -/
theorem negative_lightTransition_imbalance_le_one
    (g : Fin (m + 1) → G) {h : G}
    (q : ReducedSubsetSumCollision g h)
    (hqcard : q.val.1.card ≤ q.val.2.card)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    (hcoeff : subsetCollisionCoeffs q.val.1 q.val.2 = -c) :
    reducedCollisionImbalance q ≤ 1 := by
  have hfloor := hc.2.1 0
  have hcoeff0 := congrFun hcoeff 0
  simp only [subsetCollisionCoeffs, Fin.cons_zero, Pi.neg_apply] at hcoeff0
  have hqz := reducedCollisionImbalance_cast q hqcard
  omega

/-- The strict imbalance-drop branch of the light dynamics. -/
def ReducedCollisionImbalanceDrop
    {g : Fin (m + 1) → G} {h : G}
    (q r : ReducedSubsetSumCollision g h) : Prop :=
  reducedCollisionImbalance q + 2 ≤ reducedCollisionImbalance r

omit [DecidableEq G] in
/-- Imbalance-drop transitions cannot form a cycle or an infinite path. -/
theorem reducedCollisionImbalanceDrop_wellFounded
    {g : Fin (m + 1) → G} {h : G} :
    WellFounded (@ReducedCollisionImbalanceDrop m G _ g h) := by
  apply (measure reducedCollisionImbalance).wf.mono
  intro q r hdrop
  change reducedCollisionImbalance q < reducedCollisionImbalance r
  change reducedCollisionImbalance q + 2 ≤ reducedCollisionImbalance r at hdrop
  omega

omit [DecidableEq G] in
/-- Quantitative form of well-foundedness: a chain of `k` strict light
imbalance drops consumes at least `2k` units of its initial imbalance. -/
theorem reducedCollisionImbalanceDrop_chain_bound
    {g : Fin (m + 1) → G} {h : G}
    (r : ℕ → ReducedSubsetSumCollision g h) (k : ℕ)
    (hdrop : ∀ t < k, ReducedCollisionImbalanceDrop (r (t + 1)) (r t)) :
    2 * k + reducedCollisionImbalance (r k) ≤
      reducedCollisionImbalance (r 0) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have ih' := ih (fun t ht ↦ hdrop t (Nat.lt_trans ht (Nat.lt_succ_self k)))
      have hlast := hdrop k (Nat.lt_succ_self k)
      change reducedCollisionImbalance (r (k + 1)) + 2 ≤
        reducedCollisionImbalance (r k) at hlast
      omega

omit [DecidableEq G] in
theorem two_mul_chain_length_le_initial_imbalance
    {g : Fin (m + 1) → G} {h : G}
    (r : ℕ → ReducedSubsetSumCollision g h) (k : ℕ)
    (hdrop : ∀ t < k, ReducedCollisionImbalanceDrop (r (t + 1)) (r t)) :
    2 * k ≤ reducedCollisionImbalance (r 0) := by
  exact (Nat.le_add_right (2 * k) _).trans
    (reducedCollisionImbalanceDrop_chain_bound r k hdrop)

/-- Under common-touch failure, every canonical attachment is heavy or gives
a light transition of one of three controlled kinds: a cross-tail incidence,
a well-founded imbalance drop by at least two, or a landing at imbalance at
most one.  The sign and the shared omitted coordinate remain explicit. -/
theorem commonTouched_or_canonicalReducedCollisions_structured_light_transition
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hh0 : h ≠ 0) :
    (∃ e : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c e ≠ 0) ∨
      ∀ r : ReducedSubsetSumCollision g h,
        r ∈ canonicalReducedCollisions (g := g) hh →
        ∀ j ∈ r.val.2,
          ∃ b ∈ r.val.2, b ≠ j ∧
            ∃ c : Fin (m + 1) → ℤ,
              Witness g h c ∧ c j.succ = 0 ∧ c b.succ = -1 ∧
                ((∃ k : Fin m, 2 ≤ c k.succ) ∨
                  ∃ q : ReducedSubsetSumCollision g h,
                    q ∈ canonicalReducedCollisions (g := g) hh ∧
                      j ∉ q.val.1 ∪ q.val.2 ∧
                      ((subsetCollisionCoeffs q.val.1 q.val.2 = c ∧
                          b ∈ q.val.2) ∨
                        (subsetCollisionCoeffs q.val.1 q.val.2 = -c ∧
                          b ∈ q.val.1)) ∧
                      ((r.val.1 ∩ q.val.2).Nonempty ∨
                        ReducedCollisionImbalanceDrop q r ∨
                        reducedCollisionImbalance q ≤ 1)) := by
  rcases commonTouched_or_canonicalReducedCollisions_heavy_or_light_transition
      g hg hh hh0 with htouch | htransition
  · exact Or.inl htouch
  · right
    intro r hr j hj
    rcases htransition r hr j hj with
      ⟨b, hb, hbj, c, hc, hcj, hcb, hheavy | hlight⟩
    · exact ⟨b, hb, hbj, c, hc, hcj, hcb, Or.inl hheavy⟩
    · rcases hlight with ⟨q, hq, hjq, hsign⟩
      have hrcard := canonicalReducedCollision_card_le
        (mem_canonicalReducedCollisions_iff.mp hr)
      have hqcard := canonicalReducedCollision_card_le
        (mem_canonicalReducedCollisions_iff.mp hq)
      refine ⟨b, hb, hbj, c, hc, hcj, hcb, Or.inr
        ⟨q, hq, hjq, hsign, ?_⟩⟩
      rcases hsign with hpos | hneg
      · rcases positive_lightTransition_cross_or_imbalance_drop
          g hg hh0 r q hrcard hqcard hc hj hcj hpos.1 with hcross | hdrop
        · exact Or.inl hcross
        · exact Or.inr (Or.inl hdrop)
      · exact Or.inr (Or.inr
          (negative_lightTransition_imbalance_le_one
            g q hqcard hc hneg.1))

end MinModulus
