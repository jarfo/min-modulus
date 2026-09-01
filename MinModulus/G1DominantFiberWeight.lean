/-
# Dominant escape fibers force target padding weight

The depth-weighted estimate used to eliminate an empty positive tail does not
actually require emptiness.  For every escape target, its source-tail fiber
is contained in the full dropped root support.  Exact support exchange and
the finite root-padding complement therefore still give
`2 |fiber_q| ≤ w_q`.

Summing over the fibers covering `B_r` and applying strict majority yields
`2 |B_r| < w_r` for every genuine dominant residual.  In logarithmic form,
`|supp(r)| + log₂ |B_r| + 2 ≤ n`.
-/
import MinModulus.G1EmptyTailDepthCharge

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Every actual support-escape target has padding weight at least twice the
cardinality of the source negative-tail fiber it covers. -/
theorem two_mul_escapeFiberCard_le_targetWeight
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r q : ReducedSubsetSumCollision g h)
    (hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card)
    (hq : q ∈ canonicalSupportEscapeTargets hh r) :
    2 * (canonicalSupportEscapeTargetFiber r q).card ≤
      reducedCollisionWeight (m := m) q := by
  classical
  rcases mem_canonicalSupportEscapeTargets_iff.mp hq with ⟨j, hjq⟩
  have hjq' := mem_canonicalSupportEscapeIncidences_iff.mp hjq
  have hqcanonical := hjq'.2.1
  have hcard := hrmin q hqcanonical
  have hescape : ((q.val.1 ∪ q.val.2) \
      (r.val.1 ∪ r.val.2)).Nonempty := hjq'.2.2.2
  have hfiber : canonicalSupportEscapeTargetFiber r q =
      r.val.2 \ reducedCollisionSupport q := by
    change (if ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).Nonempty then
        r.val.2 \ (q.val.1 ∪ q.val.2) else ∅) =
      r.val.2 \ reducedCollisionSupport q
    rw [if_pos hescape]
    rfl
  have hFiberSubsetDropped : canonicalSupportEscapeTargetFiber r q ⊆
      reducedCollisionDroppedSupport r q := by
    rw [hfiber]
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_right _ hx'.1, hx'.2⟩
  have hFiberCard : (canonicalSupportEscapeTargetFiber r q).card ≤
      (reducedCollisionDroppedSupport r q).card :=
    Finset.card_mono hFiberSubsetDropped
  have hexchange :=
    card_externalSupport_eq_card_droppedSupport_add_depth r q hcard
  have hExternalSubset : reducedCollisionExternalSupport r q ⊆
      (Finset.univ : Finset (Fin m)) \ reducedCollisionSupport r := by
    intro x hx
    have hx' := Finset.mem_sdiff.mp hx
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx'.2⟩
  have hExternalCard : (reducedCollisionExternalSupport r q).card ≤
      m - (reducedCollisionSupport r).card := by
    calc
      (reducedCollisionExternalSupport r q).card ≤
          ((Finset.univ : Finset (Fin m)) \
            reducedCollisionSupport r).card :=
        Finset.card_mono hExternalSubset
      _ = m - (reducedCollisionSupport r).card := by
        rw [Finset.card_sdiff_of_subset
          (Finset.subset_univ (reducedCollisionSupport r)),
          Finset.card_univ, Fintype.card_fin]
  have hfiberDepth : (canonicalSupportEscapeTargetFiber r q).card +
      reducedCollisionSupportDepth r q ≤
        m - (reducedCollisionSupport r).card := by
    omega
  have hqCard : (reducedCollisionSupport q).card =
      (reducedCollisionSupport r).card +
        reducedCollisionSupportDepth r q := by
    simp only [reducedCollisionSupportDepth]
    omega
  have hweight : reducedCollisionWeight (m := m) q =
      2 ^ ((m - (reducedCollisionSupport r).card) -
        reducedCollisionSupportDepth r q) := by
    simp only [reducedCollisionWeight]
    rw [show (q.val.1 ∪ q.val.2).card =
        (reducedCollisionSupport r).card +
          reducedCollisionSupportDepth r q by
      simpa [reducedCollisionSupport] using hqCard]
    congr 1
    omega
  have hfiberPos : 0 < (canonicalSupportEscapeTargetFiber r q).card := by
    apply Finset.card_pos.mpr
    exact ⟨j, mem_canonicalSupportEscapeTargetFiber_iff.mpr
      ⟨hjq'.1, hjq'.2.2.1, hjq'.2.2.2⟩⟩
  have hlinear := two_mul_le_two_pow_of_pos
    (canonicalSupportEscapeTargetFiber r q).card hfiberPos
  have hpow : 2 ^ (canonicalSupportEscapeTargetFiber r q).card ≤
      2 ^ ((m - (reducedCollisionSupport r).card) -
        reducedCollisionSupportDepth r q) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hweight]
  exact hlinear.trans hpow

/-- Covered source-tail mass is bounded by the total padding weight of all
actual escape targets. -/
theorem two_mul_sourceTailCard_le_sum_escapeTargetWeights
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hrmin : ∀ u ∈ canonicalReducedCollisions (g := g) hh,
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card)
    (hcover : Finset.image Prod.fst
      (canonicalSupportEscapeIncidences hh r) = r.val.2) :
    2 * r.val.2.card ≤
      (canonicalSupportEscapeTargets hh r).sum
        (reducedCollisionWeight (m := m)) := by
  classical
  let C := canonicalReducedCollisions (g := g) hh
  let T := canonicalSupportEscapeTargets hh r
  have htailLe : r.val.2.card ≤
      (canonicalSupportEscapeIncidences hh r).card := by
    rw [← hcover]
    exact Finset.card_image_le
  have hincidenceSum : (canonicalSupportEscapeIncidences hh r).card =
      C.sum (fun q ↦ (canonicalSupportEscapeTargetFiber r q).card) :=
    card_canonicalSupportEscapeIncidences_eq_sum_targetFibers hh r
  have hpointwise : ∀ q ∈ C,
      2 * (canonicalSupportEscapeTargetFiber r q).card ≤
        if q ∈ T then reducedCollisionWeight (m := m) q else 0 := by
    intro q hqC
    by_cases hqT : q ∈ T
    · simpa [hqT] using two_mul_escapeFiberCard_le_targetWeight
        hh r q hrmin hqT
    · have hfiber : canonicalSupportEscapeTargetFiber r q = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro j hj
        have hj' := mem_canonicalSupportEscapeTargetFiber_iff.mp hj
        exact hqT (mem_canonicalSupportEscapeTargets_iff.mpr
          ⟨j, mem_canonicalSupportEscapeIncidences_iff.mpr
            ⟨hj'.1, hqC, hj'.2.1, hj'.2.2⟩⟩)
      simp [hqT, hfiber]
  have hTsub : T ⊆ C := by
    intro q hq
    rcases mem_canonicalSupportEscapeTargets_iff.mp hq with ⟨j, hj⟩
    exact (mem_canonicalSupportEscapeIncidences_iff.mp hj).2.1
  have hsumToTargets : C.sum (fun q ↦
      if q ∈ T then reducedCollisionWeight (m := m) q else 0) =
      T.sum (reducedCollisionWeight (m := m)) := by
    rw [← Finset.sum_filter]
    congr 1
    ext q
    simp only [Finset.mem_filter]
    constructor
    · exact fun hq ↦ hq.2
    · exact fun hq ↦ ⟨hTsub hq, hq⟩
  calc
    2 * r.val.2.card ≤
        2 * (canonicalSupportEscapeIncidences hh r).card :=
      Nat.mul_le_mul_left 2 htailLe
    _ = C.sum (fun q ↦
        2 * (canonicalSupportEscapeTargetFiber r q).card) := by
      rw [hincidenceSum, Finset.mul_sum]
    _ ≤ C.sum (fun q ↦
        if q ∈ T then reducedCollisionWeight (m := m) q else 0) :=
      Finset.sum_le_sum hpointwise
    _ = T.sum (reducedCollisionWeight (m := m)) := hsumToTargets

section CriticalFiberWeight

/-- Every genuine critical dominant residual satisfies
`2|B_r| < w_r`. -/
theorem two_mul_negativeTailCard_lt_weight_of_genuineDominant
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    2 * r.val.2.card < reducedCollisionWeight (m := n) r := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hq)).ne'⟩
  have hM : 0 < 2 ^ s * q :=
    mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
  have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  have hr' : r ∈ canonicalReducedCollisions (g := g)
      (half_add_half hN) := by
    simpa [criticalCanonicalReducedCollisions] using hr
  have hdominant := hres.1.1
  simp only [IsCriticalDominantEscapeCollision] at hdominant
  have hrmin : ∀ u ∈ canonicalReducedCollisions (g := g)
      (half_add_half hN),
      (reducedCollisionSupport r).card ≤
        (reducedCollisionSupport u).card := by
    simpa [criticalCanonicalReducedCollisions, reducedCollisionSupport] using
      hdominant.2.1
  have hmajor : (canonicalReducedCollisions (g := g)
      (half_add_half hN)).sum (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
    simpa [criticalCanonicalReducedCollisions] using hdominant.2.2.1
  have hcover : Finset.image Prod.fst
      (canonicalSupportEscapeIncidences (half_add_half hN) r) = r.val.2 := by
    rcases commonTouched_or_heavy_or_minSupportEscapeIncidences_cover
        g hg (half_add_half hN) (half_ne_zero hN hM) r hr' (by
          simpa [reducedCollisionSupport] using hrmin) with
      htouch | hheavy | hcover
    · exact False.elim (hres.2.1 (by
        simpa [CriticalCommonTouched] using htouch))
    · exact False.elim (hres.2.2 (by
        simpa [CriticalHeavyHalfWitness] using hheavy))
    · exact hcover.1
  have htargetWeight := two_mul_sourceTailCard_le_sum_escapeTargetWeights
    (half_add_half hN) r hrmin hcover
  let C := canonicalReducedCollisions (g := g) (half_add_half hN)
  let T := canonicalSupportEscapeTargets (half_add_half hN) r
  have hTsub : T ⊆ C.erase r := by
    intro u hu
    rcases mem_canonicalSupportEscapeTargets_iff.mp hu with ⟨j, hju⟩
    have hju' := mem_canonicalSupportEscapeIncidences_iff.mp hju
    have hur : u ≠ r := by
      intro hur
      subst u
      exact hju'.2.2.1 (Finset.mem_union_right _ hju'.1)
    exact Finset.mem_erase.mpr ⟨hur, hju'.2.1⟩
  have htargetLe : T.sum (reducedCollisionWeight (m := n)) ≤
      (C.erase r).sum (reducedCollisionWeight (m := n)) :=
    Finset.sum_le_sum_of_subset hTsub
  have herase : (C.erase r).sum (reducedCollisionWeight (m := n)) +
      reducedCollisionWeight (m := n) r =
      C.sum (reducedCollisionWeight (m := n)) :=
    Finset.sum_erase_add C (reducedCollisionWeight (m := n)) hr'
  have hmajorC : C.sum (reducedCollisionWeight (m := n)) <
      2 * reducedCollisionWeight (m := n) r := by
    simpa [C] using hmajor
  have heraseLt : (C.erase r).sum (reducedCollisionWeight (m := n)) <
      reducedCollisionWeight (m := n) r := by
    omega
  exact htargetWeight.trans_lt (htargetLe.trans_lt heraseLt)

/-- Logarithmic form of the universal fiber-weight constraint. -/
theorem supportCard_add_log_negativeTail_add_two_le_of_genuineDominant
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r) :
    (reducedCollisionSupport r).card + Nat.log 2 r.val.2.card + 2 ≤ n := by
  have hBnonempty : r.val.2.Nonempty := by
    letI : NeZero (2 ^ (s + 1) * q) :=
      ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
        (Odd.pos hq)).ne'⟩
    have hM : 0 < 2 ^ s * q :=
      mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) s) (Odd.pos hq)
    have hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
      rw [pow_succ]
      ring
    have hr' : r ∈ canonicalReducedCollisions (g := g)
        (half_add_half hN) := by
      simpa [criticalCanonicalReducedCollisions] using hr
    exact canonicalReducedCollision_negative_tail_nonempty
      g hg (half_add_half hN) (half_ne_zero hN hM) hr'
  have hweightBound :=
    two_mul_negativeTailCard_lt_weight_of_genuineDominant
      hq g hg r hr hres
  have hweight : reducedCollisionWeight (m := n) r =
      2 ^ (n - (reducedCollisionSupport r).card) := by
    rfl
  rw [hweight] at hweightBound
  have hlogPow : 2 ^ Nat.log 2 r.val.2.card ≤ r.val.2.card :=
    Nat.pow_log_le_self 2 (Finset.card_ne_zero.mpr hBnonempty)
  have hlogSuccPow : 2 ^ (Nat.log 2 r.val.2.card + 1) ≤
      2 * r.val.2.card := by
    rw [pow_succ]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left 2 hlogPow
  have hpowers : 2 ^ (Nat.log 2 r.val.2.card + 1) <
      2 ^ (n - (reducedCollisionSupport r).card) :=
    hlogSuccPow.trans_lt hweightBound
  have hexponents : Nat.log 2 r.val.2.card + 1 <
      n - (reducedCollisionSupport r).card :=
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp hpowers
  have hsupport : (reducedCollisionSupport r).card ≤ n := by
    simpa [reducedCollisionSupport] using
      Finset.card_le_univ (reducedCollisionSupport r)
  omega

/-- Critical localization with the universal dominant-fiber weight and its
logarithmic support consequence retained in the surviving branch. -/
theorem critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_fiberWeight
    {n s q : ℕ} (hn : 1 ≤ n) (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ (s + 1) * q < stratumBound (n + 1) (s + 1)) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      CriticalCommonTouched g ∨ CriticalHeavyHalfWitness g ∨
      ∃ r ∈ criticalCanonicalReducedCollisions g,
        IsCriticalGenuineDominantEscapeCollision g r ∧
          r.val.1.Nonempty ∧
          2 * r.val.2.card < reducedCollisionWeight (m := n) r ∧
          (reducedCollisionSupport r).card +
              Nat.log 2 r.val.2.card + 2 ≤ n := by
  rcases
      critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_positiveTail
        hn hq g hg hcritical with
    hcross | htouch | hheavy | ⟨r, hr, hres, hpositive⟩
  · exact Or.inl hcross
  · exact Or.inr (Or.inl htouch)
  · exact Or.inr (Or.inr (Or.inl hheavy))
  · exact Or.inr (Or.inr (Or.inr ⟨r, hr, hres, hpositive,
      two_mul_negativeTailCard_lt_weight_of_genuineDominant
        hq g hg r hr hres,
      supportCard_add_log_negativeTail_add_two_le_of_genuineDominant
        hq g hg r hr hres⟩))

end CriticalFiberWeight

end MinModulus
