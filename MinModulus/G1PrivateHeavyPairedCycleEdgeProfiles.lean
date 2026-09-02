/-
# Profile reduction for paired heavy cycle edges

The repeated-cycle endpoint retains two distinct tail-heavy vertices together
with the fixed algebra on their incoming edges.  This module compares each
incoming package with the repeated omission `z`.

If the package's shared omission is `z`, its source-private, target-private,
and source-avoiding witnesses all retain that exact label.  Otherwise the
heavy target private witness has two distinct known omissions; it either has
a third omission or its exact positive mass is a pure coefficient-two edge.
Applying this reduction to both incoming packages leaves one paired hard core:
both canonical witness triples share the repeated omission `z`.
-/
import MinModulus.G1PrivateHeavyRepeatedCycleEdgeAlgebra
import MinModulus.G1ProfilePureEdgeLightSplit

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- The three canonical witnesses on the incoming edge of cycle vertex `i`
all omit the specified coordinate `z`. -/
def MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i : Fin d) (z : Fin (m + 1)) : Prop :=
  let p := (finRotate d).symm i
  let b := minimalSupportPrivateShiftCycleVertex g hno hmin a p
  let u := minimalSupportPrivateShiftCycleVertex g hno hmin a i
  minimalSupportPrivateWitness g h hmin b z = -1 ∧
    minimalSupportPrivateWitness g h hmin u z = -1 ∧
    minimalSupportAvoidingWitness g hno b z = -1

/-- The heavy target private witness at cycle vertex `i` is the pure edge
with omission pair `{z,x}` and a tail coefficient-two center. -/
def MinimalSupportPrivateShiftCycleTargetPurePairAt
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i : Fin d) (z : Fin (m + 1)) : Prop :=
  let u := minimalSupportPrivateShiftCycleVertex g hno hmin a i
  let cu := minimalSupportPrivateWitness g h hmin u
  ∃ x : Fin (m + 1), ∃ e : Fin m,
    x ≠ z ∧ e.succ ≠ z ∧ e.succ ≠ x ∧
      (∀ y, cu y = -1 ↔ y = z ∨ y = x) ∧
      cu e.succ = 2 ∧ cu = pureEdgeCoeffs e.succ z x

/-- A retained target-pure-pair package is, in particular, the established
tail-heavy pure-edge residual. -/
theorem MinimalSupportPrivateShiftCycleTargetPurePairAt.tailHeavyPureEdge
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i : Fin d) (z : Fin (m + 1))
    (hpure : MinimalSupportPrivateShiftCycleTargetPurePairAt
      g h hno hmin a i z) :
    WitnessTailHeavyPureEdge g h := by
  obtain ⟨x, e, hxz, hez, hex, homit, heTwo, hshape⟩ := hpure
  exact ⟨minimalSupportPrivateWitness g h hmin
      (minimalSupportPrivateShiftCycleVertex g hno hmin a i),
    e.succ, z, x,
    minimalSupportPrivateWitness_isWitness g h hmin
      (minimalSupportPrivateShiftCycleVertex g hno hmin a i),
    hez, hex, Ne.symm hxz, hshape, e, by omega⟩

/-- Compare one incoming heavy-edge package with a known omission `z` of its
target private witness.  A different shared label gives either a third
omission or a retained exact pure-pair profile. -/
theorem minimalSupportPrivateShiftCycleIncomingHeavyEdgeAlgebra_at_omission
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (a : ↥B) {d : ℕ} (i : Fin d) (z : Fin (m + 1))
    (hincoming : MinimalSupportPrivateShiftCycleIncomingHeavyEdgeAlgebra
      g h hno hmin a i)
    (huz : minimalSupportPrivateWitness g h hmin
      (minimalSupportPrivateShiftCycleVertex g hno hmin a i) z = -1) :
    MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
        g hno hmin a i z ∨
      WitnessExactOmissionTriangle g h ∨
      WitnessThreeDistinctOmissions g h ∨
      MinimalSupportPrivateShiftCycleTargetPurePairAt
        g h hno hmin a i z := by
  let p := (finRotate d).symm i
  let b := minimalSupportPrivateShiftCycleVertex g hno hmin a p
  let u := minimalSupportPrivateShiftCycleVertex g hno hmin a i
  change u ∈ minimalSupportPrivateTailHeavyVertices g h hmin ∧
      minimalSupportTransversalShiftTarget g hno hmin b = u ∧
      (MinimalSupportPrivateShiftEdgeThreeSharedOmission g hno hmin b ∨
        WitnessExactOmissionTriangle g h ∨
        WitnessThreeDistinctOmissions g h) at hincoming
  rcases hincoming with ⟨huHeavy, htarget, hshared | htriangle | hthree⟩
  · obtain ⟨x, hcbx, hcux, hrbx⟩ := hshared
    have huz' : minimalSupportPrivateWitness g h hmin u z = -1 := by
      simpa [u] using huz
    have hcux' : minimalSupportPrivateWitness g h hmin u x = -1 := by
      rw [← htarget]
      exact hcux
    by_cases hxz : x = z
    · subst x
      exact Or.inl ⟨hcbx, huz, hrbx⟩
    · rcases exactPairOmissions_or_threeDistinctOmissions
          g (minimalSupportPrivateWitness_isWitness g h hmin u)
            (Ne.symm hxz) huz' hcux' with hexact | hthree
      · obtain ⟨e, heHeavy⟩ :=
          (mem_minimalSupportPrivateTailHeavyVertices_iff
            g h hmin u).mp huHeavy
        have hez : e.succ ≠ z := by
          intro hez
          rw [hez] at heHeavy
          have := huz'
          omega
        have hex : e.succ ≠ x := by
          intro hex
          rw [hex] at heHeavy
          omega
        have heCases := witness_coeff_eq_zero_or_one_or_two_of_exact_pair
          g (minimalSupportPrivateWitness_isWitness g h hmin u)
            z x e.succ (Ne.symm hxz) hexact hez hex
        have heTwo : minimalSupportPrivateWitness g h hmin u e.succ = 2 := by
          rcases heCases with heZero | heOne | heTwo <;> omega
        have hshape := exactPair_coeff_two_eq_pureEdgeCoeffs
          g (minimalSupportPrivateWitness_isWitness g h hmin u)
            z x e.succ (Ne.symm hxz) hexact hez hex heTwo
        exact Or.inr (Or.inr (Or.inr
          ⟨x, e, hxz, hez, hex, hexact, heTwo, hshape⟩))
      · exact Or.inr (Or.inr (Or.inl hthree))
  · exact Or.inr (Or.inl htriangle)
  · exact Or.inr (Or.inr (Or.inl hthree))

/-- The hard paired residual after comparing both incoming packages with the
repeated label: both canonical incoming-edge triples share `z`. -/
def MinimalSupportPrivateShiftCyclePairedIncomingEdgesShareRepeatedOmission
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
    MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a (finRotate d j) z ∧
    MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt
      g hno hmin a i z

/-- Normalize both fixed-edge trichotomies in a paired repeated-label package.
Unless an established triangle, three-omission, or pure-edge frontier occurs,
both incoming witness triples share the repeated omission itself. -/
theorem minimalSupportPrivateShiftCycle_pairedHeavyIncomingEdgeAlgebra_profiles
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
    (hpair :
      MinimalSupportPrivateShiftCycleRepeatedLabelPairedHeavyIncomingEdgeAlgebra
        g hg hh hno hmin a z k l) :
    MinimalSupportPrivateShiftCyclePairedIncomingEdgesShareRepeatedOmission
        g hg hh hno hmin a z k l ∨
      WitnessExactOmissionTriangle g h ∨
      WitnessThreeDistinctOmissions g h ∨
      WitnessTailHeavyPureEdge g h := by
  obtain ⟨j, i, hjPair, hjFiber, hji, hjHeavyEndpoint, hiHeavyEndpoint,
    hsubset, _hthree, _hjAlgebra, hiAlgebra⟩ := hpair
  have hjEndpoint := (Finset.mem_inter.mp hjHeavyEndpoint).1
  have hjHeavy := (Finset.mem_inter.mp hjHeavyEndpoint).2
  have hiEndpoint := (Finset.mem_inter.mp hiHeavyEndpoint).1
  have hjOmit := hsubset hjEndpoint
  have hiOmit := hsubset hiEndpoint
  have hjz := (mem_minimalSupportPrivateOmissionVertices_iff
    g hmin z
      (minimalSupportPrivateShiftCycleVertex g hno hmin a
        (finRotate d j))).mp hjOmit
  have hiz := (mem_minimalSupportPrivateOmissionVertices_iff
    g hmin z
      (minimalSupportPrivateShiftCycleVertex g hno hmin a i)).mp hiOmit
  have hjIncoming := minimalSupportPrivateShiftCycle_incomingHeavyEdgeAlgebra
    g hg hh hno hmin a hcycle (finRotate d j) hjHeavy
  rcases minimalSupportPrivateShiftCycleIncomingHeavyEdgeAlgebra_at_omission
      g hno hmin a (finRotate d j) z hjIncoming hjz with
    hjShared | htriangle | hthree | hjPure
  · rcases minimalSupportPrivateShiftCycleIncomingHeavyEdgeAlgebra_at_omission
        g hno hmin a i z hiAlgebra hiz with
      hiShared | htriangle | hthree | hiPure
    · exact Or.inl ⟨j, i, hjPair, hjFiber, hji, hjShared, hiShared⟩
    · exact Or.inr (Or.inl htriangle)
    · exact Or.inr (Or.inr (Or.inl hthree))
    · exact Or.inr (Or.inr (Or.inr
        (hiPure.tailHeavyPureEdge g hno hmin a i z)))
  · exact Or.inr (Or.inl htriangle)
  · exact Or.inr (Or.inr (Or.inl hthree))
  · exact Or.inr (Or.inr (Or.inr
      (hjPure.tailHeavyPureEdge g hno hmin a (finRotate d j) z)))

/-- Global-facing profile endpoint for the cycle count.  Outside the explicit
two-cycle, capacity, crossing, and already-established structural profiles,
both retained incoming-edge witness triples share the repeated label `z`. -/
theorem critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_pairedSharedOmission
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
        MinimalSupportPrivateShiftCyclePairedIncomingEdgesShareRepeatedOmission
          g hg (half_add_half (by rw [pow_succ]; ring))
            hno hmin a z k l := by
  rcases
      critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_pairedHeavyIncomingEdgeAlgebra
        hq g hg hno hmin a hcycle L hcount hB with
    htwo | hcapacity | hcross | ⟨z, k, l, hzB, hkl, hk, hl, hpair⟩
  · exact Or.inl htwo
  · exact Or.inr (Or.inl hcapacity)
  · exact Or.inr (Or.inr (Or.inl hcross))
  · rcases minimalSupportPrivateShiftCycle_pairedHeavyIncomingEdgeAlgebra_profiles
        g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin a
          hcycle z k l hpair with hshared | htriangle | hthree | hpure
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨z, k, l, hzB, hkl, hk, hl, hshared⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl htriangle)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hthree))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hpure)))))

end MinModulus
