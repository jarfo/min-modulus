/-
# Packing equal avoiding profiles on a private shift cycle

An incoming avoiding witness is zero at its edge source and nonzero at its
target.  The same coefficient vector therefore cannot label two consecutive
incoming targets.  Each fixed avoiding-profile fiber is an independent set
of the displayed cycle, so its rotated copy is disjoint and
`2 * |fiber| <= d`.

This closes the equal-profile half of the paired shared-omission comparison.
The unequal half retains the two localized directed coefficient gaps.
-/
import MinModulus.G1PrivateHeavyPairedSharedOmissionAlgebra

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Cycle target indices whose incoming edge has one fixed avoiding-witness
coefficient profile. -/
noncomputable def minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : Fin (m + 1) → ℤ) : Finset (Fin d) := by
  classical
  exact Finset.univ.filter fun i ↦
    minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a i = r

@[simp] theorem mem_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_iff
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) (d : ℕ) (r : Fin (m + 1) → ℤ) (i : Fin d) :
    i ∈ minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d r ↔
      minimalSupportPrivateShiftCycleIncomingAvoidingWitness
        g hno hmin a i = r := by
  classical
  simp [minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber]

/-- Consecutive incoming targets cannot have the same avoiding profile: the
first witness is nonzero at its target, while the second is zero there as its
source. -/
theorem minimalSupportPrivateShiftCycleIncomingAvoidingWitness_ne_rotate
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (i : Fin d) :
    minimalSupportPrivateShiftCycleIncomingAvoidingWitness
        g hno hmin a i ≠
      minimalSupportPrivateShiftCycleIncomingAvoidingWitness
        g hno hmin a (finRotate d i) := by
  let p := (finRotate d).symm i
  let b := minimalSupportPrivateShiftCycleVertex g hno hmin a p
  let u := minimalSupportPrivateShiftCycleVertex g hno hmin a i
  let bnext := minimalSupportPrivateShiftCycleVertex g hno hmin a
    ((finRotate d).symm (finRotate d i))
  have htarget : minimalSupportTransversalShiftTarget g hno hmin b = u := by
    have hp : finRotate d p = i := (finRotate d).apply_symm_apply i
    simpa [b, u, hp] using
      minimalSupportPrivateShiftCycleTarget_eq_vertex_rotate
        g hno hmin a hcycle p
  have hbnext : bnext = u := by
    exact congrArg
      (minimalSupportPrivateShiftCycleVertex g hno hmin a)
      ((finRotate d).symm_apply_apply i)
  have hnz := minimalSupportAvoidingWitness_target_ne_zero
    g hno hmin b
  rw [htarget] at hnz
  have hzero : minimalSupportAvoidingWitness g hno bnext bnext = 0 :=
    minimalSupportAvoidingWitness_eq_zero g hno bnext
  have hzeroAtU : minimalSupportAvoidingWitness g hno bnext u = 0 := by
    rw [← hbnext]
    exact hzero
  intro heq
  apply hnz
  have heqU := congrFun heq u
  change minimalSupportAvoidingWitness g hno b u =
      minimalSupportAvoidingWitness g hno bnext u at heqU
  rw [hzeroAtU] at heqU
  exact heqU

/-- A fixed incoming avoiding-profile fiber is disjoint from its cyclic
rotation. -/
theorem disjoint_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_image_rotate
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : Fin (m + 1) → ℤ) :
    Disjoint
      (minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d r)
      ((minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d r).image (finRotate d)) := by
  classical
  apply Finset.disjoint_left.mpr
  intro i hi hiRotate
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hiRotate
  have hjProfile :=
    (mem_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_iff
      g hno hmin a d r j).mp hj
  have hrotateProfile :=
    (mem_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_iff
      g hno hmin a d r (finRotate d j)).mp hi
  exact (minimalSupportPrivateShiftCycleIncomingAvoidingWitness_ne_rotate
    g hno hmin a hcycle j) (hjProfile.trans hrotateProfile.symm)

/-- Uniform cycle-wide reuse bound for one complete incoming avoiding-witness
profile. -/
theorem two_mul_card_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_le
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (r : Fin (m + 1) → ℤ) :
    2 * (minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d r).card ≤ d := by
  classical
  let S := minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
    g hno hmin a d r
  have hdisjoint : Disjoint S (S.image (finRotate d)) := by
    simpa [S] using
      disjoint_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_image_rotate
        g hno hmin a hcycle r
  have hcardImage : (S.image (finRotate d)).card = S.card :=
    Finset.card_image_of_injective S (finRotate d).injective
  have hsubset : S ∪ S.image (finRotate d) ⊆
      (Finset.univ : Finset (Fin d)) := Finset.subset_univ _
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_union_of_disjoint hdisjoint, hcardImage,
    Finset.card_univ, Fintype.card_fin] at hcard
  change 2 * S.card ≤ d
  omega

/-- The paired comparison with a repeated equal avoiding profile, including
the cycle-wide packing bound for its complete coefficient fiber. -/
def MinimalSupportPrivateShiftCyclePairedSharedEqualAvoidingProfile
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (z : Fin (m + 1)) (k l : Fin d) : Prop :=
  ∃ j i : Fin d, ∃ r : Fin (m + 1) → ℤ,
    (j = k ∨ j = l) ∧
    j ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg hh hno hmin a d z ∧
    finRotate d j ≠ i ∧
    (i = k ∨ i = finRotate d k ∨ i = l ∨ i = finRotate d l) ∧
    MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a (finRotate d j) z ∧
    MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a i z ∧
    finRotate d j ∈
      minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d r ∧
    i ∈ minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
        g hno hmin a d r ∧
    2 ≤ (minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d r).card ∧
    2 * (minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
      g hno hmin a d r).card ≤ d

/-- The unequal half of the paired comparison, retaining the finite endpoint
position and the two localized directed gaps. -/
def MinimalSupportPrivateShiftCyclePairedSharedDirectedAvoidingGaps
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (z : Fin (m + 1)) (k l : Fin d) : Prop :=
  ∃ j i : Fin d,
    (j = k ∨ j = l) ∧
    j ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
      g hg hh hno hmin a d z ∧
    finRotate d j ≠ i ∧
    (i = k ∨ i = finRotate d k ∨ i = l ∨ i = finRotate d l) ∧
    MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a (finRotate d j) z ∧
    MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a i z ∧
    MinimalSupportPrivateShiftCycleIncomingAvoidingDirectedGapsAt
      g hno hmin a (finRotate d j) i z

/-- Split the paired comparison into a cycle-packed equal-profile branch and
the retained directed-gap branch. -/
theorem minimalSupportPrivateShiftCycle_pairedSharedAvoidingComparison_packedProfile_or_directedGaps
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (z : Fin (m + 1)) (k l : Fin d)
    (hcomparison : MinimalSupportPrivateShiftCyclePairedSharedAvoidingComparison
      g hg hh hno hmin a z k l) :
    MinimalSupportPrivateShiftCyclePairedSharedEqualAvoidingProfile
        g hg hh hno hmin a z k l ∨
      MinimalSupportPrivateShiftCyclePairedSharedDirectedAvoidingGaps
        g hg hh hno hmin a z k l := by
  obtain ⟨j, i, hdata⟩ := hcomparison
  have hjPair := hdata.1
  have hjFiber := hdata.2.1
  have hji := hdata.2.2.1
  have hiPosition := hdata.2.2.2.1
  have hjShared := hdata.2.2.2.2.2.2.1
  have hiShared := hdata.2.2.2.2.2.2.2.1
  have hprofileOrGaps := hdata.2.2.2.2.2.2.2.2
  rcases hprofileOrGaps with hprofile | hgaps
  · left
    let r := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
      g hno hmin a (finRotate d j)
    have hjMem : finRotate d j ∈
        minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
          g hno hmin a d r := by
      simp [r]
    have hiMem : i ∈
        minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
          g hno hmin a d r := by
      rw [mem_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_iff]
      exact hprofile.symm
    have htwo : 2 ≤
        (minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber
          g hno hmin a d r).card := by
      have hone := Finset.one_lt_card.mpr
        ⟨finRotate d j, hjMem, i, hiMem, hji⟩
      omega
    exact ⟨j, i, r, hjPair, hjFiber, hji, hiPosition,
      hjShared, hiShared, hjMem, hiMem, htwo,
      two_mul_card_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_le
        g hno hmin a hcycle r⟩
  · right
    exact ⟨j, i, hjPair, hjFiber, hji, hiPosition,
      hjShared, hiShared, hgaps⟩

/-- Global-facing cycle endpoint after closing equal-profile reuse by cyclic
packing.  The last residual is now explicitly a packed equal profile or the
localized directed-gap branch. -/
theorem critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_packedAvoidingProfile_or_directedGaps
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (L : ℕ) (hcount : L < d)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    d = 2 ∨ B.card + L ≤ n + 1 ∨
      criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      WitnessExactOmissionTriangle g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessThreeDistinctOmissions g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      WitnessTailHeavyPureEdge g
        ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) ∨
      ∃ z : Fin (n + 1), ∃ k l : Fin d,
        z ∉ B ∧ k ≠ l ∧
        k ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        l ∈ minimalSupportPrivateShiftCycleEdgeLabelFiber
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a d z ∧
        (MinimalSupportPrivateShiftCyclePairedSharedEqualAvoidingProfile
            g hg (half_add_half (by rw [pow_succ]; ring))
              hno hmin a z k l ∨
          MinimalSupportPrivateShiftCyclePairedSharedDirectedAvoidingGaps
            g hg (half_add_half (by rw [pow_succ]; ring))
              hno hmin a z k l) := by
  rcases
      critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_pairedSharedAvoidingComparison
        hq g hg hno hmin a hcycle L hcount hB with
    htwo | hcapacity | hcross | htriangle | hthree | hpure |
      ⟨z, k, l, hzB, hkl, hk, hl, hcomparison⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcapacity)
  · exact Or.inr (Or.inr (Or.inl hcross))
  · exact Or.inr (Or.inr (Or.inr (Or.inl htriangle)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hthree))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpure)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨z, k, l, hzB, hkl, hk, hl,
        minimalSupportPrivateShiftCycle_pairedSharedAvoidingComparison_packedProfile_or_directedGaps
          g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a
            hcycle z k l hcomparison⟩)))))

end MinModulus
