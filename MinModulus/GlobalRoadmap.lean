/-
# Interfaces for the global min-modulus roadmap

This file packages the three remaining conjectural inputs separately from the
proved descent machinery.  The stratified induction uses
`CriticalRangeCommonTouchedHalfWitnesses`, after the unrestricted common-touch
statement was refuted by `G1Counterexample.lean`.
-/
import MinModulus.QuadraticWedge
import MinModulus.G1DominantPadding
import MinModulus.UniqueSums

namespace MinModulus

open Finset

/-- A cyclic modulus `N` admits a valid tuple of length `n`. -/
def AdmitsValidTuple (n N : ℕ) : Prop :=
  ∃ g : Fin n → ZMod N, ValidTuple g

/-- The fixed-set bound from the paper, used to state the exceptional lift
modulus in G3. -/
def globalBound (n : ℕ) : ℕ :=
  2 ^ n - 2 ^ Nat.log 2 n

/-- The predicted lower bound in the exact `2^s * q` stratum (`q` odd).
For `s ≤ log₂ n` this is the endpoint `2^n - 2^s`; afterwards it is the
global envelope `globalBound n`. -/
def stratumBound (n s : ℕ) : ℕ :=
  2 ^ n - 2 ^ min s (Nat.log 2 n)

/-- Transport the paper's fixed super-increasing validity predicate to the
group-theoretic `ValidTuple` predicate used by the descent. -/
theorem validTuple_fixed_of_valid {n N : ℕ} (hv : Valid n N) :
    ValidTuple (fun i : Fin n => (a i.val : ZMod N)) := by
  intro k hksum hkval
  let K : ℕ → ℕ := fun i => if hi : i < n then k ⟨i, hi⟩ else 0
  have hKsum : dsum n K = n := by
    unfold dsum
    rw [← Fin.sum_univ_eq_sum_range]
    simpa [K] using hksum
  have hcast :
      ((∑ i : Fin n, k i * a i.val : ℕ) : ZMod N)
        = ((∑ i : Fin n, a i.val : ℕ) : ZMod N) := by
    push_cast
    simpa [nsmul_eq_mul] using hkval
  have hleft :
      (∑ i ∈ range n, K i * a i) = ∑ i : Fin n, k i * a i.val := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i _
    simp [K]
  have hright : (∑ i ∈ range n, a i) = ∑ i : Fin n, a i.val := by
    rw [← Fin.sum_univ_eq_sum_range]
  have hmod : (∑ i ∈ range n, K i * a i) ≡ (∑ i ∈ range n, a i) [MOD N] := by
    rw [hleft, hright]
    rw [← ZMod.natCast_eq_natCast_iff]
    exact hcast
  have hones := hv K hKsum hmod
  intro i
  simpa [K, i.isLt] using hones i.val i.isLt

/-- Every power-gap endpoint from `valid_gap` therefore admits a valid tuple
in the group-theoretic formulation. -/
theorem admitsValidTuple_gap {n t : ℕ} (hn : 2 ≤ n) (htn : 2 ^ t ≤ n) :
    AdmitsValidTuple n (2 ^ n - 2 ^ t) :=
  ⟨_, validTuple_fixed_of_valid (valid_gap hn htn)⟩

/-- **Unrestricted common touch (false).**  This was the original G1 form and
is retained to state its counterexample and the generic descent consequence.
The global induction below assumes only
`CriticalRangeCommonTouchedHalfWitnesses`. -/
def CommonTouchedHalfWitnesses : Prop :=
  ∀ {n M : ℕ} (_hM : 0 < M) (g : Fin (n + 1) → ZMod (2 * M)),
    ValidTuple g →
    (∃ c : Fin (n + 1) → ℤ, Witness g (M : ZMod (2 * M)) c) →
    ∃ j : Fin (n + 1),
      ∀ c : Fin (n + 1) → ℤ, Witness g (M : ZMod (2 * M)) c → c j ≠ 0

/-- **G1 in the exact range needed by the stratified induction.**  At the
`(s+1)`-st two-adic step, common touch is required only while the modulus is
strictly below that stratum's claimed endpoint.  Unlike the unrestricted
`CommonTouchedHalfWitnesses`, this statement is not refuted by the valid
seven-tuple modulo `1006` in `G1Counterexample.lean`. -/
def CriticalRangeCommonTouchedHalfWitnesses : Prop :=
  ∀ {n s q : ℕ} (_hq : Odd q)
    (_hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1))
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)),
    ValidTuple g →
    (∃ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c) →
    ∃ j : Fin (n + 1),
      ∀ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c j ≠ 0

/-- In the critical range, the subset-sum cube overlaps its half translate in
more than the exact power of two omitted from the claimed stratum endpoint.
This is the quantitative input absent from unrestricted G1. -/
theorem critical_subsetSum_half_overlap
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    2 ^ min (s + 1) (Nat.log 2 (n + 1)) <
      ((subsetSumRange g) ∩ (subsetSumShiftRange g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))).card := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hlog : Nat.log 2 (n + 1) ≤ n := by
    have := Nat.log_lt_self 2 (by omega : n + 1 ≠ 0)
    omega
  have hmin : min (s + 1) (Nat.log 2 (n + 1)) ≤ n :=
    (min_le_right _ _).trans hlog
  have hp : 2 ^ min (s + 1) (Nat.log 2 (n + 1)) ≤ 2 ^ (n + 1) :=
    (Nat.pow_le_pow_right (by omega) hmin).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have hendpoint : stratumBound (n + 1) (s + 1) +
      2 ^ min (s + 1) (Nat.log 2 (n + 1)) = 2 ^ (n + 1) := by
    unfold stratumBound
    exact Nat.sub_add_cancel hp
  apply subsetSumShift_overlap_card_gt_of_add_lt g hg
  omega

/-- The half-translate overlap is a union of free two-element orbits.  For a
nontrivial tuple the omitted power of two is even, so the strict critical
overlap bound improves from one extra point to two. -/
theorem critical_subsetSum_half_overlap_add_two_le
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    2 ^ min (s + 1) (Nat.log 2 (n + 1)) + 2 ≤
      ((subsetSumRange g) ∩ (subsetSumShiftRange g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))).card := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hlog : 0 < Nat.log 2 (n + 1) :=
    Nat.log_pos (by norm_num) (by omega)
  have hmin : min (s + 1) (Nat.log 2 (n + 1)) ≠ 0 := by
    omega
  have hK : Even (2 ^ min (s + 1) (Nat.log 2 (n + 1))) := by
    rw [Nat.even_pow]
    exact ⟨by norm_num, hmin⟩
  apply add_two_le_card_subsetSumOverlap_of_even_lt g hg
    (half_add_half hN) (half_ne_zero hN hM) hK
  exact critical_subsetSum_half_overlap hq g hg hcritical

/-- Critical G1 in reduced-shape form: the exact padding weights of all
disjoint half-collision shapes exceed the endpoint gap by at least two.  This
is the quantitative interface for the next support-incidence argument. -/
theorem critical_reduced_collision_weight_lower_bound
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    2 ^ min (s + 1) (Nat.log 2 (n + 1)) + 2 ≤
      ∑ r : ReducedSubsetSumCollision g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        2 ^ (n - (r.val.1 ∪ r.val.2).card) := by
  rw [← card_subsetSumOverlap_eq_sum_reduced_weights g hg
    ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))]
  exact critical_subsetSum_half_overlap_add_two_le hn hq g hg hcritical

/-- Canonical representatives of the reduced half-collision swap pairs at a
critical two-adic step.  Their negative tails form an intersecting family. -/
noncomputable def criticalCanonicalReducedCollisions
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) :
    Finset (ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))) :=
  canonicalReducedCollisions (g := g)
    (half_add_half (M := 2 ^ s * q) (by rw [pow_succ]; ring))

/-- Ordered distinct pairs in the critical canonical collision family. -/
noncomputable def criticalCanonicalDistinctCollisionPairs
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) :=
  canonicalDistinctReducedCollisionPairs (g := g)
    (half_add_half (M := 2 ^ s * q) (by rw [pow_succ]; ring))

/-- Oriented positive-to-negative crossings in the critical canonical
collision family. -/
noncomputable def criticalCanonicalPositiveNegativeCrossPairs
    {n s q : ℕ} (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) :=
  canonicalPositiveNegativeCrossPairs (g := g)
    (half_add_half (M := 2 ^ s * q) (by rw [pow_succ]; ring))

/-- Every unordered pair of distinct critical canonical shapes crosses in at
least one orientation.  Both the unweighted count and the exact product-
padding weight therefore have density at least one half. -/
theorem critical_canonicalCrossPairs_dense
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g) :
    (criticalCanonicalDistinctCollisionPairs g).card ≤
        2 * (criticalCanonicalPositiveNegativeCrossPairs g).card ∧
      (criticalCanonicalDistinctCollisionPairs g).sum (fun p ↦
          reducedCollisionWeight (m := n) p.1 *
            reducedCollisionWeight (m := n) p.2) ≤
        2 * (criticalCanonicalPositiveNegativeCrossPairs g).sum (fun p ↦
          reducedCollisionWeight (m := n) p.1 *
            reducedCollisionWeight (m := n) p.2) := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  constructor
  · simpa [criticalCanonicalDistinctCollisionPairs,
      criticalCanonicalPositiveNegativeCrossPairs] using
      card_canonicalDistinctPairs_le_two_mul_crossPairs
        g hg (half_add_half hN) (half_ne_zero hN hM)
  · simpa [criticalCanonicalDistinctCollisionPairs,
      criticalCanonicalPositiveNegativeCrossPairs] using
      sum_canonicalDistinctPairWeights_le_two_mul_crossPairWeights
        g hg (half_add_half hN) (half_ne_zero hN hM)

/-- The critical endpoint gap plus two is bounded by twice the exact padding
weight of the canonical intersecting representatives. -/
theorem critical_canonicalReducedCollision_weight_lower_bound
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    2 ^ min (s + 1) (Nat.log 2 (n + 1)) + 2 ≤
      2 * (criticalCanonicalReducedCollisions g).sum
        (fun r ↦ reducedCollisionWeight (m := n) r) := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  calc
    2 ^ min (s + 1) (Nat.log 2 (n + 1)) + 2 ≤
        ∑ r : ReducedSubsetSumCollision g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
          2 ^ (n - (r.val.1 ∪ r.val.2).card) :=
      critical_reduced_collision_weight_lower_bound hn hq g hg hcritical
    _ = 2 * (canonicalReducedCollisions (g := g)
          (half_add_half hN)).sum
            (fun r ↦ reducedCollisionWeight (m := n) r) := by
      simpa [criticalCanonicalReducedCollisions,
        reducedCollisionWeight] using
        sum_reducedCollisionWeight_eq_two_mul_canonical
          (g := g) (half_add_half hN) (half_ne_zero hN hM)

/-- After cancelling the factor two, the canonical intersecting family alone
carries at least half the endpoint-gap weight plus one. -/
theorem critical_canonicalReducedCollision_weight_half_lower_bound
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1 ≤
      (criticalCanonicalReducedCollisions g).sum
        (fun r ↦ reducedCollisionWeight (m := n) r) := by
  let a := min (s + 1) (Nat.log 2 (n + 1))
  have hlog : 0 < Nat.log 2 (n + 1) :=
    Nat.log_pos (by norm_num) (by omega)
  have ha : 0 < a := by
    dsimp [a]
    omega
  have hpow : 2 ^ a + 2 = 2 * (2 ^ (a - 1) + 1) := by
    have ha' : a = (a - 1) + 1 := by omega
    conv_lhs => lhs; rw [ha', pow_succ]
    ring
  have hdouble := critical_canonicalReducedCollision_weight_lower_bound
    hn hq g hg hcritical
  change 2 ^ a + 2 ≤
      2 * (criticalCanonicalReducedCollisions g).sum
        (fun r ↦ reducedCollisionWeight (m := n) r) at hdouble
  rw [hpow] at hdouble
  exact Nat.le_of_mul_le_mul_left hdouble (by norm_num)

/-- Squaring the critical half-gap lower bound and using dense canonical
crossings leaves exactly one loss term: the sum of squared padding weights on
the diagonal. -/
theorem critical_square_gap_le_two_crossMass_add_diagonal
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) *
        (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) ≤
      2 * (criticalCanonicalPositiveNegativeCrossPairs g).sum (fun p ↦
        reducedCollisionWeight (m := n) p.1 *
          reducedCollisionWeight (m := n) p.2) +
        (criticalCanonicalReducedCollisions g).sum (fun r ↦
          reducedCollisionWeight (m := n) r *
            reducedCollisionWeight (m := n) r) := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hweight := critical_canonicalReducedCollision_weight_half_lower_bound
    hn hq g hg hcritical
  have hsquare := Nat.mul_le_mul hweight hweight
  have hmass := square_sum_canonicalWeights_le_two_crossMass_add_diagonal
    g hg (half_add_half hN) (half_ne_zero hN hM)
  exact hsquare.trans (by
    simpa [criticalCanonicalReducedCollisions,
      criticalCanonicalPositiveNegativeCrossPairs] using hmass)

/-- Critical quantitative split: either oriented crossings already carry one
quarter of the squared half-gap, or the diagonal padding weights carry one
half.  Controlling the second concentration branch is now the exact remaining
loss before a crossing-based critical G1 count. -/
theorem critical_crossingMass_or_diagonalConcentration
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) *
        (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) ≤
      4 * (criticalCanonicalPositiveNegativeCrossPairs g).sum (fun p ↦
        reducedCollisionWeight (m := n) p.1 *
          reducedCollisionWeight (m := n) p.2) ∨
    (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) *
        (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) ≤
      2 * (criticalCanonicalReducedCollisions g).sum (fun r ↦
        reducedCollisionWeight (m := n) r *
          reducedCollisionWeight (m := n) r) := by
  have htotal := critical_square_gap_le_two_crossMass_add_diagonal
    hn hq g hg hcritical
  omega

/-- The critical canonical collision family is nonempty; quantitatively it
already carries at least the half-gap weight plus one. -/
theorem criticalCanonicalReducedCollisions_nonempty
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    (criticalCanonicalReducedCollisions g).Nonempty := by
  have hweight := critical_canonicalReducedCollision_weight_half_lower_bound
    hn hq g hg hcritical
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty.mp hne] at hweight
  simp at hweight

/-- Diagonal concentration produces one explicit maximum-weight canonical
collision.  Its padding weight controls the diagonal relative to the actual
total canonical weight; the ambient-order estimate is retained as a weaker
corollary rather than used as the main structural information. -/
theorem critical_diagonalConcentration_exists_dominantCollision
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1))
    (hdiagonal :
      (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) *
          (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) ≤
        2 * (criticalCanonicalReducedCollisions g).sum (fun r ↦
          reducedCollisionWeight (m := n) r *
            reducedCollisionWeight (m := n) r)) :
    ∃ r ∈ criticalCanonicalReducedCollisions g,
      (∀ u ∈ criticalCanonicalReducedCollisions g,
        reducedCollisionWeight (m := n) u ≤
          reducedCollisionWeight (m := n) r) ∧
      (∀ u ∈ criticalCanonicalReducedCollisions g,
        (r.val.1 ∪ r.val.2).card ≤ (u.val.1 ∪ u.val.2).card) ∧
      (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) *
          (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) ≤
        2 * (reducedCollisionWeight (m := n) r *
          (criticalCanonicalReducedCollisions g).sum
            (reducedCollisionWeight (m := n))) ∧
      (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) *
          (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) ≤
        (2 ^ (s + 1) * q) *
          2 ^ (n - (r.val.1 ∪ r.val.2).card) := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hne : (canonicalReducedCollisions (g := g)
      (half_add_half hN)).Nonempty := by
    simpa [criticalCanonicalReducedCollisions] using
      criticalCanonicalReducedCollisions_nonempty hn hq g hg hcritical
  obtain ⟨r, hr, hrIsMax, hrMinSupport, hrdiag⟩ :=
    exists_canonical_weight_mul_sum_ge_diagonal
      (g := g) (half_add_half hN) hne
  have hupper := two_mul_sum_canonicalWeights_le_card
    g hg (half_add_half hN) (half_ne_zero hN hM)
  have hrIsMax' : ∀ u ∈ criticalCanonicalReducedCollisions g,
      reducedCollisionWeight (m := n) u ≤
        reducedCollisionWeight (m := n) r := by
    simpa [criticalCanonicalReducedCollisions] using hrIsMax
  have hrMinSupport' : ∀ u ∈ criticalCanonicalReducedCollisions g,
      (r.val.1 ∪ r.val.2).card ≤ (u.val.1 ∪ u.val.2).card := by
    simpa [criticalCanonicalReducedCollisions] using hrMinSupport
  have hrdiag' :
      (criticalCanonicalReducedCollisions g).sum (fun u ↦
          reducedCollisionWeight (m := n) u *
            reducedCollisionWeight (m := n) u) ≤
        reducedCollisionWeight (m := n) r *
          (criticalCanonicalReducedCollisions g).sum
            (reducedCollisionWeight (m := n)) := by
    simpa [criticalCanonicalReducedCollisions] using hrdiag
  have hupper' :
      2 * (criticalCanonicalReducedCollisions g).sum
          (reducedCollisionWeight (m := n)) ≤ 2 ^ (s + 1) * q := by
    simpa [criticalCanonicalReducedCollisions, ZMod.card] using hupper
  refine ⟨r, by simpa [criticalCanonicalReducedCollisions] using hr,
    hrIsMax', hrMinSupport', ?_, ?_⟩
  · calc
    (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) *
          (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) ≤
        2 * (criticalCanonicalReducedCollisions g).sum (fun u ↦
          reducedCollisionWeight (m := n) u *
            reducedCollisionWeight (m := n) u) := hdiagonal
    _ ≤ 2 * (reducedCollisionWeight (m := n) r *
          (criticalCanonicalReducedCollisions g).sum
            (reducedCollisionWeight (m := n))) :=
      Nat.mul_le_mul_left 2 hrdiag'
  · calc
    (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) *
          (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) ≤
        2 * (criticalCanonicalReducedCollisions g).sum (fun u ↦
          reducedCollisionWeight (m := n) u *
            reducedCollisionWeight (m := n) u) := hdiagonal
    _ ≤ 2 * (reducedCollisionWeight (m := n) r *
          (criticalCanonicalReducedCollisions g).sum
            (reducedCollisionWeight (m := n))) :=
      Nat.mul_le_mul_left 2 hrdiag'
    _ = reducedCollisionWeight (m := n) r *
          (2 * (criticalCanonicalReducedCollisions g).sum
            (reducedCollisionWeight (m := n))) := by ring
    _ ≤ reducedCollisionWeight (m := n) r * (2 ^ (s + 1) * q) :=
      Nat.mul_le_mul_left _ hupper'
    _ = (2 ^ (s + 1) * q) *
          2 ^ (n - (r.val.1 ∪ r.val.2).card) := by
      simp [reducedCollisionWeight, Nat.mul_comm]

/-- The diagonal sum has now been eliminated from the critical interface:
either crossing product mass is large, or one explicit maximum-weight
canonical collision controls the concentration relative to total weight. -/
theorem critical_crossingMass_or_exists_dominantCollision
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) *
        (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) ≤
      4 * (criticalCanonicalPositiveNegativeCrossPairs g).sum (fun p ↦
        reducedCollisionWeight (m := n) p.1 *
          reducedCollisionWeight (m := n) p.2) ∨
    ∃ r ∈ criticalCanonicalReducedCollisions g,
      (∀ u ∈ criticalCanonicalReducedCollisions g,
        reducedCollisionWeight (m := n) u ≤
          reducedCollisionWeight (m := n) r) ∧
      (∀ u ∈ criticalCanonicalReducedCollisions g,
        (r.val.1 ∪ r.val.2).card ≤ (u.val.1 ∪ u.val.2).card) ∧
      (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) *
          (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) ≤
        2 * (reducedCollisionWeight (m := n) r *
          (criticalCanonicalReducedCollisions g).sum
            (reducedCollisionWeight (m := n))) ∧
      (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) *
          (2 ^ (min (s + 1) (Nat.log 2 (n + 1)) - 1) + 1) ≤
        (2 ^ (s + 1) * q) *
          2 ^ (n - (r.val.1 ∪ r.val.2).card) := by
  rcases critical_crossingMass_or_diagonalConcentration
      hn hq g hg hcritical with hcross | hdiagonal
  · exact Or.inl hcross
  · exact Or.inr
      (critical_diagonalConcentration_exists_dominantCollision
        hn hq g hg hcritical hdiagonal)

/-- Critical-range G1 is reduced to two explicit quantitative escape
branches: a genuinely heavy half-witness or a positive-tail crossing between
distinct canonical reduced collisions.  The residual all-light/non-crossing
unit matrix has been eliminated. -/
theorem critical_commonTouched_or_heavy_halfWitness_or_distinctCanonicalCross
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    (∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c → c e ≠ 0) ∨
      (∃ c : Fin (n + 1) → ℤ,
        Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c ∧
          ∃ k : Fin n, 2 ≤ c k.succ) ∨
      ∃ r : ReducedSubsetSumCollision g
          ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
        r ∈ criticalCanonicalReducedCollisions g ∧
          ∃ q' : ReducedSubsetSumCollision g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)),
            q' ∈ criticalCanonicalReducedCollisions g ∧ q' ≠ r ∧
              LightTransitionCrossesPositiveTail r q' := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hne : (canonicalReducedCollisions (g := g)
      (half_add_half hN)).Nonempty := by
    simpa [criticalCanonicalReducedCollisions] using
      criticalCanonicalReducedCollisions_nonempty hn hq g hg hcritical
  simpa [criticalCanonicalReducedCollisions] using
    (commonTouched_or_heavy_halfWitness_or_distinctCanonicalCross
      g hg (half_add_half hN) (half_ne_zero hN hM) hne)

/-- The critical canonical representatives have pairwise-intersecting
negative tails. -/
theorem criticalCanonicalReducedCollisions_negative_tails_inter
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    {r₁ r₂ : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))}
    (hr₁ : r₁ ∈ criticalCanonicalReducedCollisions g)
    (hr₂ : r₂ ∈ criticalCanonicalReducedCollisions g) :
    (r₁.val.2 ∩ r₂.val.2).Nonempty := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  apply canonicalReducedCollision_negative_tails_inter
    g hg (half_add_half hN) (half_ne_zero hN hM) r₁ r₂
  · simpa [criticalCanonicalReducedCollisions] using hr₁
  · simpa [criticalCanonicalReducedCollisions] using hr₂

/-- If critical G1 common touch fails, the endpoint-gap mass transfers to
explicit ordered attachment incidences internal to the canonical negative
tails.  Any completion may therefore focus on bounding how many incidences
one attached witness can realize, or on turning them into a disjoint layer. -/
theorem critical_internalAttachmentPairs_weight_lower_bound_of_no_common_touched
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1))
    (hno : ¬∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c →
        c e ≠ 0) :
    2 ^ min (s + 1) (Nat.log 2 (n + 1)) + 2 ≤
      (criticalCanonicalReducedCollisions g).sum (fun r ↦
        reducedCollisionWeight (m := n) r *
          (reducedCollisionInternalAttachmentPairs g
            ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r).card) := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  calc
    2 ^ min (s + 1) (Nat.log 2 (n + 1)) + 2 ≤
        2 * (criticalCanonicalReducedCollisions g).sum
          (fun r ↦ reducedCollisionWeight (m := n) r) :=
      critical_canonicalReducedCollision_weight_lower_bound
        hn hq g hg hcritical
    _ ≤ (criticalCanonicalReducedCollisions g).sum (fun r ↦
          reducedCollisionWeight (m := n) r *
            (reducedCollisionInternalAttachmentPairs g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r).card) := by
      simpa [criticalCanonicalReducedCollisions] using
        two_mul_sum_canonical_weight_le_sum_internalAttachmentPairs_weight
          g hg (half_add_half hN) (half_ne_zero hN hM) hno

/-- Operational critical G1 frontier: either common touch already gives the
deletion coordinate, or the canonical tails carry endpoint-gap-many weighted
internal attachment incidences. -/
theorem commonTouched_or_critical_internalAttachmentPairs_weight_lower_bound
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    (∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c →
        c e ≠ 0) ∨
      2 ^ min (s + 1) (Nat.log 2 (n + 1)) + 2 ≤
        (criticalCanonicalReducedCollisions g).sum (fun r ↦
          reducedCollisionWeight (m := n) r *
            (reducedCollisionInternalAttachmentPairs g
              ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r).card) := by
  by_cases htouch : ∃ e : Fin (n + 1), ∀ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c →
        c e ≠ 0
  · exact Or.inl htouch
  · exact Or.inr
      (critical_internalAttachmentPairs_weight_lower_bound_of_no_common_touched
        hn hq g hg hcritical htouch)

/-- Consequently every critical-range valid tuple has a half-witness already
in the translated subset-sum layer.  All non-anchor coefficients can be
chosen in `{-1,0,1}`. -/
theorem exists_light_half_witness_of_critical_range
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    ∃ c : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) c ∧
      ∀ j : Fin n, -1 ≤ c j.succ ∧ c j.succ ≤ 1 := by
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hsmall : 2 ^ (s + 1) * q < 2 ^ (n + 1) :=
    hcritical.trans_le (Nat.sub_le _ _)
  exact exists_light_half_witness_of_lt_two_pow hN hM g hg hsmall

/-- **G2, odd-base form.**  A valid `n`-tuple modulo an odd number forces the
odd modulus to be at least `2^n - 1`. -/
def OddStratumLowerBound : Prop :=
  ∀ {n N : ℕ}, Odd N → AdmitsValidTuple n N → 2 ^ n - 1 ≤ N

/-- **G3, exceptional-lift form.**  Away from powers of two, no valid
`n`-tuple exists at the one high-valuation modulus where deletion gives only
`2 * B(n-1)` rather than `B(n)`.  `2^log₂(n) ≠ n` is the arithmetic form of
"`n` is not a power of two" used by the paper. -/
def ExceptionalLiftObstruction : Prop :=
  ∀ n : ℕ, 2 ≤ n → 2 ^ Nat.log 2 n ≠ n →
    ¬AdmitsValidTuple n (2 * globalBound (n - 1))

/-- G1 plus the proved quotient lemmas gives the load-bearing dichotomy:
halving either preserves the tuple length or deletes exactly one coordinate. -/
theorem admits_half_or_delete_of_g1 (hG1 : CommonTouchedHalfWitnesses)
    {n M : ℕ} (hM : 0 < M) (hvalid : AdmitsValidTuple (n + 1) (2 * M)) :
    AdmitsValidTuple (n + 1) M ∨ AdmitsValidTuple n M := by
  obtain ⟨g, hg⟩ := hvalid
  by_cases hw : ∃ c : Fin (n + 1) → ℤ, Witness g (M : ZMod (2 * M)) c
  · right
    obtain ⟨j, hj⟩ := hG1 hM g hg hw
    exact exists_validTuple_half_of_delete (N := 2 * M) (M := M) rfl hM hg j hj
  · left
    apply exists_validTuple_half_of_no_witness (N := 2 * M) (M := M) rfl hM hg
    intro c hc
    exact hw ⟨c, hc⟩

/-- Critical-range G1 always takes the deletion branch.  The subset-sum
overlap theorem supplies a light half-witness automatically, so the
no-witness/length-preserving halving branch cannot occur below the claimed
stratum endpoint. -/
theorem admits_delete_of_critical_g1
    (hG1 : CriticalRangeCommonTouchedHalfWitnesses)
    {n s q : ℕ} (hq : Odd q)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1))
    (hvalid : AdmitsValidTuple (n + 1) (2 ^ (s + 1) * q)) :
    AdmitsValidTuple n (2 ^ s * q) := by
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  obtain ⟨g, hg⟩ := hvalid
  obtain ⟨c, hc, _⟩ :=
    exists_light_half_witness_of_critical_range hq g hg hcritical
  obtain ⟨j, hj⟩ := hG1 hq hcritical g hg ⟨c, hc⟩
  exact exists_validTuple_half_of_delete
    (N := 2 ^ (s + 1) * q) (M := 2 ^ s * q) hN hM hg j hj

/-- Compatibility form of `admits_delete_of_critical_g1`: the old dichotomy
still holds, but its critical-range proof always inhabits the deletion side. -/
theorem admits_half_or_delete_of_critical_g1
    (hG1 : CriticalRangeCommonTouchedHalfWitnesses)
    {n s q : ℕ} (hq : Odd q)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1))
    (hvalid : AdmitsValidTuple (n + 1) (2 ^ (s + 1) * q)) :
    AdmitsValidTuple (n + 1) (2 ^ s * q) ∨
      AdmitsValidTuple n (2 ^ s * q) :=
  Or.inr (admits_delete_of_critical_g1 hG1 hq hcritical hvalid)

/-- The corrected three roadmap gaps imply the complete stratified lower bound.  This
packages the induction that was previously only described in the handoff.

The exceptional use of G3 is forced precisely when deletion occurs after the
valuation has reached `log₂ n` and `n` is not a power of two.  The induction
then gives `M ≥ globalBound (n-1)`.  Both sides are multiples of `2^log₂ n`,
so either equality holds (excluded by G3) or the next multiple already lies
above the required stratum endpoint. -/
theorem stratum_lower_bound_of_gaps
    (hG1 : CriticalRangeCommonTouchedHalfWitnesses)
    (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction) :
    ∀ {n s q : ℕ}, 2 ≤ n → Odd q → AdmitsValidTuple n (2 ^ s * q) →
      stratumBound n s ≤ 2 ^ s * q := by
  intro n s
  induction s generalizing n with
  | zero =>
      intro q hn hq hv
      have h := hG2 hq (by simpa using hv)
      simpa [stratumBound] using h
  | succ s ih =>
      intro q hn hq hv
      by_cases hcritical : 2 ^ (s + 1) * q < stratumBound n (s + 1)
      swap
      · omega
      let M := 2 ^ s * q
      have hv2 : AdmitsValidTuple n (2 * M) := by
        simpa [M, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hv
      have hnform : n - 1 + 1 = n := by omega
      have hdelete := admits_delete_of_critical_g1 hG1
        (n := n - 1) (s := s) (q := q) hq
        (by simpa [hnform] using hcritical)
        (by simpa [hnform] using hv)
      exact (by
        by_cases hn2 : n = 2
        · subst hn2
          have hlog22 : Nat.log 2 2 = 1 :=
            Nat.log_eq_of_pow_le_of_lt_pow (by norm_num) (by norm_num)
          have hb : stratumBound 2 (s + 1) = 2 := by
            rw [stratumBound, hlog22, min_eq_right (show 1 ≤ s + 1 by omega)]
            norm_num
          rw [hb]
          calc
            2 ≤ 2 ^ (s + 1) := by
              rw [pow_succ]
              exact Nat.le_mul_of_pos_left 2 (pow_pos (by omega) s)
            _ ≤ 2 ^ (s + 1) * q := Nat.le_mul_of_pos_right _ (Odd.pos hq)
        · have hnprev : 2 ≤ n - 1 := by omega
          have hih := ih hnprev hq (by simpa [M] using hdelete)
          let m := Nat.log 2 n
          have hm_lt : m < n := Nat.log_lt_self 2 (by omega)
          have hpred_ne : n - 1 ≠ 0 := by omega
          have hlog_adj : Nat.log 2 (n - 1) = m ↔ 2 ^ m ≠ n := by
            simpa [m, Nat.sub_add_cancel (by omega : 1 ≤ n)] using
              (Nat.log_eq_log_succ_iff (b := 2) (n := n - 1) (by omega) hpred_ne)
          by_cases hpow : 2 ^ m = n
          · have hmpos : 0 < m := by
              apply Nat.pos_of_ne_zero
              intro hm0
              have hn1 : n = 1 := by simpa [hm0] using hpow.symm
              omega
            have hmform : m = m - 1 + 1 := by omega
            have hp_pos : 0 < 2 ^ (m - 1) := pow_pos (by omega) _
            have hp_split : 2 ^ m = 2 ^ (m - 1) * 2 := by
              calc
                2 ^ m = 2 ^ (m - 1 + 1) := congrArg (fun e => 2 ^ e) hmform
                _ = 2 ^ (m - 1) * 2 := pow_succ 2 (m - 1)
            have hp_low : 2 ^ (m - 1) ≤ n - 1 := by omega
            have hp_high : n - 1 < 2 ^ (m - 1 + 1) := by
              rw [← hmform, hpow]
              omega
            have hlogpred : Nat.log 2 (n - 1) = m - 1 :=
              Nat.log_eq_of_pow_le_of_lt_pow hp_low hp_high
            have hexp : min s (m - 1) + 1 = min (s + 1) m := by omega
            have hpow_n : 2 ^ n = 2 * 2 ^ (n - 1) := by
              calc
                2 ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
                _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
                _ = 2 * 2 ^ (n - 1) := by omega
            have hstep : stratumBound n (s + 1) = 2 * stratumBound (n - 1) s := by
              unfold stratumBound
              rw [hlogpred]
              rw [hpow_n, ← hexp]
              rw [show 2 ^ (min s (m - 1) + 1) =
                2 * 2 ^ min s (m - 1) by rw [pow_succ]; omega]
              omega
            rw [hstep]
            calc
              2 * stratumBound (n - 1) s ≤ 2 * M := Nat.mul_le_mul_left 2 hih
              _ = 2 ^ (s + 1) * q := by
                simp [M, pow_succ, Nat.mul_left_comm, Nat.mul_comm]
          · have hlogpred : Nat.log 2 (n - 1) = m := hlog_adj.mpr hpow
            by_cases hs : s < m
            · have hexp : min s m + 1 = min (s + 1) m := by omega
              have hpow_n : 2 ^ n = 2 * 2 ^ (n - 1) := by
                calc
                  2 ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
                  _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
                  _ = 2 * 2 ^ (n - 1) := by omega
              have hstep : stratumBound n (s + 1) =
                  2 * stratumBound (n - 1) s := by
                unfold stratumBound
                rw [hlogpred]
                rw [hpow_n, ← hexp]
                rw [show 2 ^ (min s m + 1) = 2 * 2 ^ min s m by
                  rw [pow_succ]; omega]
                omega
              rw [hstep]
              calc
                2 * stratumBound (n - 1) s ≤ 2 * M := Nat.mul_le_mul_left 2 hih
                _ = 2 ^ (s + 1) * q := by
                  simp [M, pow_succ, Nat.mul_left_comm, Nat.mul_comm]
            · have hms : m ≤ s := by omega
              have hprev : stratumBound (n - 1) s = globalBound (n - 1) := by
                simp [stratumBound, globalBound, hlogpred, min_eq_right hms]
              have hcur : stratumBound n (s + 1) = globalBound n := by
                have hmss : m ≤ s + 1 := by omega
                simp [stratumBound, globalBound, m, min_eq_right hmss]
              have hCM : globalBound (n - 1) ≤ M := by simpa [hprev, M] using hih
              have hMne : M ≠ globalBound (n - 1) := by
                intro heq
                exact (hG3 n hn hpow) (by simpa [heq] using hv2)
              have hCltM : globalBound (n - 1) < M := lt_of_le_of_ne hCM (Ne.symm hMne)
              have hm_pred : m ≤ n - 1 := by omega
              have hdvdM : 2 ^ m ∣ M := by
                refine ⟨2 ^ (s - m) * q, ?_⟩
                have hsform : s = m + (s - m) := by omega
                have hpows : 2 ^ s = 2 ^ m * 2 ^ (s - m) := by
                  calc
                    2 ^ s = 2 ^ (m + (s - m)) := congrArg (fun e => 2 ^ e) hsform
                    _ = 2 ^ m * 2 ^ (s - m) := pow_add 2 m (s - m)
                calc
                  M = 2 ^ s * q := rfl
                  _ = (2 ^ m * 2 ^ (s - m)) * q := by rw [hpows]
                  _ = 2 ^ m * (2 ^ (s - m) * q) := by ring
              have hdvdC : 2 ^ m ∣ globalBound (n - 1) := by
                refine ⟨2 ^ (n - 1 - m) - 1, ?_⟩
                unfold globalBound
                rw [hlogpred]
                have hnform' : n - 1 = m + (n - 1 - m) := by omega
                have hpown' : 2 ^ (n - 1) = 2 ^ m * 2 ^ (n - 1 - m) := by
                  calc
                    2 ^ (n - 1) = 2 ^ (m + (n - 1 - m)) :=
                      congrArg (fun e => 2 ^ e) hnform'
                    _ = 2 ^ m * 2 ^ (n - 1 - m) := pow_add 2 m (n - 1 - m)
                calc
                  2 ^ (n - 1) - 2 ^ m =
                      2 ^ m * 2 ^ (n - 1 - m) - 2 ^ m := by rw [hpown']
                  _ = 2 ^ m * (2 ^ (n - 1 - m) - 1) := by
                    rw [Nat.mul_sub_left_distrib, mul_one]
              obtain ⟨u, hu⟩ := hdvdM
              obtain ⟨v, hv⟩ := hdvdC
              have huv : v + 1 ≤ u := by
                rw [hu, hv] at hCltM
                exact Nat.succ_le_iff.mpr ((Nat.mul_lt_mul_left (pow_pos (by omega) m)).mp hCltM)
              have hgap : globalBound (n - 1) + 2 ^ m ≤ M := by
                rw [hu, hv]
                calc
                  2 ^ m * v + 2 ^ m = 2 ^ m * (v + 1) := by ring
                  _ ≤ 2 ^ m * u := Nat.mul_le_mul_left _ huv
              have hCsum : globalBound (n - 1) + 2 ^ m = 2 ^ (n - 1) := by
                unfold globalBound
                rw [hlogpred]
                have hp_le : 2 ^ m ≤ 2 ^ (n - 1) :=
                  Nat.pow_le_pow_right (by omega) hm_pred
                exact Nat.sub_add_cancel hp_le
              have hpow_n : 2 ^ n = 2 * 2 ^ (n - 1) := by
                calc
                  2 ^ n = 2 ^ (n - 1 + 1) := by congr 1; omega
                  _ = 2 ^ (n - 1) * 2 := pow_succ 2 (n - 1)
                  _ = 2 * 2 ^ (n - 1) := by omega
              rw [hcur]
              calc
                globalBound n ≤ 2 ^ n := Nat.sub_le _ _
                _ = 2 * 2 ^ (n - 1) := hpow_n
                _ ≤ 2 * M := by rw [← hCsum]; exact Nat.mul_le_mul_left 2 hgap
                _ = 2 ^ (s + 1) * q := by
                  simp [M, pow_succ, Nat.mul_left_comm, Nat.mul_comm]
      )

/-- Conditional form of Conjecture 1: once critical-range G1, G2, and G3 are
proved, every positive modulus admitting a valid `n`-tuple is at least
`globalBound n`. -/
theorem global_lower_bound_of_gaps
    (hG1 : CriticalRangeCommonTouchedHalfWitnesses)
    (hG2 : OddStratumLowerBound)
    (hG3 : ExceptionalLiftObstruction)
    {n N : ℕ} (hn : 2 ≤ n) (hN : 0 < N) (hv : AdmitsValidTuple n N) :
    globalBound n ≤ N := by
  obtain ⟨s, q, hq, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hN.ne'
  have hs := stratum_lower_bound_of_gaps hG1 hG2 hG3 hn hq hv
  have hmin : min s (Nat.log 2 n) ≤ Nat.log 2 n := min_le_right _ _
  have hp : 2 ^ min s (Nat.log 2 n) ≤ 2 ^ Nat.log 2 n :=
    Nat.pow_le_pow_right (by omega) hmin
  exact (Nat.sub_le_sub_left hp (2 ^ n)).trans hs

end MinModulus
