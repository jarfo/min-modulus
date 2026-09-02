/-
# Algebra in the paired shared-omission cycle core

The remaining repeated-cycle hard core contains two distinct heavy target
vertices whose incoming source-private, target-private, and source-avoiding
witnesses all omit one repeated external label `z`.

This module retains the exact four-position endpoint overlap and compares the
two avoiding witnesses.  They either coincide as a fixed coefficient profile,
or validity forces coefficient gaps in both directions.  The two gap labels
are distinct, avoid `z`, and cannot be the source at which the upper witness
is canonically zero.
-/
import MinModulus.G1PrivateHeavyPairedCycleEdgeProfiles
import MinModulus.G1PrivateHeavyJointFiberAlgebra

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The avoiding witness attached to the incoming edge of cycle vertex `i`. -/
noncomputable def minimalSupportPrivateShiftCycleIncomingAvoidingWitness
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i : Fin d) : Fin (m + 1) → ℤ :=
  minimalSupportAvoidingWitness g hno
    (minimalSupportPrivateShiftCycleVertex g hno hmin a
      ((finRotate d).symm i))

/-- The coefficient-gap alternative for two incoming avoiding witnesses.
The directed gap coordinates are distinct, avoid the shared omission, and
avoid the source coordinate of the upper witness. -/
def MinimalSupportPrivateShiftCycleIncomingAvoidingDirectedGapsAt
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i j : Fin d) (z : Fin (m + 1)) : Prop :=
  let bi := minimalSupportPrivateShiftCycleVertex g hno hmin a
    ((finRotate d).symm i)
  let bj := minimalSupportPrivateShiftCycleVertex g hno hmin a
    ((finRotate d).symm j)
  let ri := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
    g hno hmin a i
  let rj := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
    g hno hmin a j
  ∃ x y : Fin (m + 1),
    ri x + 2 ≤ rj x ∧ rj y + 2 ≤ ri y ∧
      x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ≠ bj ∧ y ≠ bi

/-- Every endpoint vertex has one of the four cycle indices displayed by the
two original repeated-label edges. -/
theorem minimalSupportPrivateShiftCycleIndex_fourPosition_of_mem_edgePairEndpointOwners
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ}
    (hcycle : IsMinimalFixedPointFreeCycle
      (minimalSupportTransversalShiftTarget g hno hmin) a d)
    (k l i : Fin d)
    (hi : minimalSupportPrivateShiftCycleVertex g hno hmin a i ∈
      minimalSupportPrivateShiftCycleEdgePairEndpointOwners
        g hno hmin a k l) :
    i = k ∨ i = finRotate d k ∨ i = l ∨ i = finRotate d l := by
  have hinjective := minimalSupportPrivateShiftCycleVertex_injective
    g hno hmin a hcycle
  simp only [minimalSupportPrivateShiftCycleEdgePairEndpointOwners,
    Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with hik | hik | hil | hil
  · exact Or.inl (hinjective hik)
  · right; left
    apply hinjective
    exact hik.trans
      (minimalSupportPrivateShiftCycleTarget_eq_vertex_rotate
        g hno hmin a hcycle k)
  · right; right; left
    exact hinjective hil
  · right; right; right
    apply hinjective
    exact hil.trans
      (minimalSupportPrivateShiftCycleTarget_eq_vertex_rotate
        g hno hmin a hcycle l)

/-- Two incoming avoiding witnesses which share `z` either agree completely
or expose two distinct directed coefficient gaps away from `z` and from the
opposite source zeros. -/
theorem minimalSupportPrivateShiftCycle_incomingAvoidingWitnesses_eq_or_directedGaps
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i j : Fin d) (z : Fin (m + 1))
    (hiShared : MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a i z)
    (hjShared : MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a j z) :
    minimalSupportPrivateShiftCycleIncomingAvoidingWitness
        g hno hmin a i =
      minimalSupportPrivateShiftCycleIncomingAvoidingWitness
        g hno hmin a j ∨
      MinimalSupportPrivateShiftCycleIncomingAvoidingDirectedGapsAt
        g hno hmin a i j z := by
  let bi := minimalSupportPrivateShiftCycleVertex g hno hmin a
    ((finRotate d).symm i)
  let bj := minimalSupportPrivateShiftCycleVertex g hno hmin a
    ((finRotate d).symm j)
  let ri := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
    g hno hmin a i
  let rj := minimalSupportPrivateShiftCycleIncomingAvoidingWitness
    g hno hmin a j
  have hri : Witness g h ri := by
    exact minimalSupportAvoidingWitness_isWitness g hno bi
  have hrj : Witness g h rj := by
    exact minimalSupportAvoidingWitness_isWitness g hno bj
  have hriz : ri z = -1 := hiShared.2.2
  have hrjz : rj z = -1 := hjShared.2.2
  by_cases heq : ri = rj
  · exact Or.inl heq
  · right
    obtain ⟨x, hx⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
      g hg hri hrj heq
    obtain ⟨y, hy⟩ := exists_coefficient_add_two_le_of_distinct_witnesses
      g hg hrj hri (Ne.symm heq)
    have hxy : x ≠ y := by
      intro hxy
      subst y
      omega
    have hxz : x ≠ z := by
      intro hxz
      subst x
      omega
    have hyz : y ≠ z := by
      intro hyz
      subst y
      omega
    have hxbj : x ≠ bj := by
      intro hxbj
      subst x
      have hrjZero := minimalSupportAvoidingWitness_eq_zero g hno bj
      have hriFloor := hri.2.1 bj
      change rj bj = 0 at hrjZero
      omega
    have hybi : y ≠ bi := by
      intro hybi
      subst y
      have hriZero := minimalSupportAvoidingWitness_eq_zero g hno bi
      have hrjFloor := hrj.2.1 bi
      change ri bi = 0 at hriZero
      omega
    exact ⟨x, y, hx, hy, hxy, hxz, hyz, hxbj, hybi⟩

/-- The paired common-`z` core, enriched with the exact endpoint position of
the second target and the equality-or-directed-gap comparison of the two
incoming avoiding witnesses. -/
def MinimalSupportPrivateShiftCyclePairedSharedAvoidingComparison
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
    minimalSupportPrivateShiftCycleEdgePairEndpointOwners
        g hno hmin a k l ⊆
      minimalSupportPrivateOmissionVertices g hmin z ∧
    3 ≤ (minimalSupportPrivateOmissionVertices g hmin z).card ∧
    MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a (finRotate d j) z ∧
    MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a i z ∧
    (minimalSupportPrivateShiftCycleIncomingAvoidingWitness
          g hno hmin a (finRotate d j) =
        minimalSupportPrivateShiftCycleIncomingAvoidingWitness
          g hno hmin a i ∨
      MinimalSupportPrivateShiftCycleIncomingAvoidingDirectedGapsAt
        g hno hmin a (finRotate d j) i z)

/-- Enrich the paired common-label core with its finite endpoint-overlap and
avoiding-witness coefficient comparison. -/
theorem minimalSupportPrivateShiftCycle_pairedSharedOmission_avoidingComparison
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
    (hshared :
      MinimalSupportPrivateShiftCyclePairedIncomingEdgesShareRepeatedOmission
        g hg hh hno hmin a z k l) :
    MinimalSupportPrivateShiftCyclePairedSharedAvoidingComparison
      g hg hh hno hmin a z k l := by
  obtain ⟨j, i, hdata⟩ := hshared
  have hjPair := hdata.1
  have hjFiber := hdata.2.1
  have hji := hdata.2.2.1
  have hiHeavy := hdata.2.2.2.2.1
  have hsubset := hdata.2.2.2.2.2.1
  have hthree := hdata.2.2.2.2.2.2.1
  have hjShared := hdata.2.2.2.2.2.2.2.1
  have hiShared := hdata.2.2.2.2.2.2.2.2
  have hiEndpoint := (Finset.mem_inter.mp hiHeavy).1
  have hiPosition :=
    minimalSupportPrivateShiftCycleIndex_fourPosition_of_mem_edgePairEndpointOwners
      g hno hmin a hcycle k l i hiEndpoint
  have hcomparison :=
    minimalSupportPrivateShiftCycle_incomingAvoidingWitnesses_eq_or_directedGaps
      g hg hno hmin a (finRotate d j) i z hjShared hiShared
  exact ⟨j, i, hjPair, hjFiber, hji, hiPosition, hsubset, hthree,
    hjShared, hiShared, hcomparison⟩

/-- Global-facing refinement of the paired profile endpoint.  The only new
residual now retains a finite four-position overlap and either one common
avoiding-witness profile or two localized directed coefficient gaps. -/
theorem critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_pairedSharedAvoidingComparison
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
        MinimalSupportPrivateShiftCyclePairedSharedAvoidingComparison
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a z k l := by
  rcases
      critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_pairedSharedOmission
        hq g hg hno hmin a hcycle L hcount hB with
    htwo | hcapacity | hcross | htriangle | hthree | hpure |
      ⟨z, k, l, hzB, hkl, hk, hl, hshared⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcapacity)
  · exact Or.inr (Or.inr (Or.inl hcross))
  · exact Or.inr (Or.inr (Or.inr (Or.inl htriangle)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hthree))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpure)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      ⟨z, k, l, hzB, hkl, hk, hl,
        minimalSupportPrivateShiftCycle_pairedSharedOmission_avoidingComparison
          g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a
            hcycle z k l hshared⟩)))))

end MinModulus
