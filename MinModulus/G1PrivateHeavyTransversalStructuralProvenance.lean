/-
# Provenance retained by the global heavy-target collapse

The preceding target-collapse theorem returned broad three-omission and
pure-edge propositions.  For deletion these are too lossy: the witness must
remain identified as the canonical private witness at the selected target,
and the deterministic external shift-edge label must remain one of its
omissions.

This file repeats the short heavy-witness normalization while retaining that
data.  The resulting critical residual is parameterized by the original
minimal transversal and carries an explicit source, its selected target, the
edge label, and the exact target-private coefficient vector.
-/
import MinModulus.G1PrivateHeavyTransversalTargetCollapse

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- The canonical private witness at the selected target of `b` has three
displayed pairwise-distinct omissions, one of which is the retained edge
label `z`. -/
def MinimalSupportTransversalShiftTargetThreeOmissionsAt
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1)) : Prop :=
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let c := minimalSupportPrivateWitness g h hmin u
  ∃ x y : Fin (m + 1),
    z ≠ x ∧ z ≠ y ∧ x ≠ y ∧
      c z = -1 ∧ c x = -1 ∧ c y = -1

/-- The canonical private witness at the selected target of `b` is an exact
pure edge whose first retained omission is the edge label `z`. -/
def MinimalSupportTransversalShiftTargetPurePairAt
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1)) : Prop :=
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let c := minimalSupportPrivateWitness g h hmin u
  ∃ x : Fin (m + 1), ∃ e : Fin m,
    x ≠ z ∧ e.succ ≠ z ∧ e.succ ≠ x ∧
      (∀ y, c y = -1 ↔ y = z ∨ y = x) ∧
      c e.succ = 2 ∧ c = pureEdgeCoeffs e.succ z x

omit [DecidableEq G] in
/-- Forgetting the provenance gives the established global three-omission
profile. -/
theorem MinimalSupportTransversalShiftTargetThreeOmissionsAt.threeDistinct
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1))
    (hthree : MinimalSupportTransversalShiftTargetThreeOmissionsAt
      g h hno hmin b z) :
    WitnessThreeDistinctOmissions g h := by
  obtain ⟨x, y, hzx, hzy, hxy, hcz, hcx, hcy⟩ := hthree
  exact ⟨minimalSupportPrivateWitness g h hmin
      (minimalSupportTransversalShiftTarget g hno hmin b),
    z, x, y,
    minimalSupportPrivateWitness_isWitness g h hmin
      (minimalSupportTransversalShiftTarget g hno hmin b),
    hzx, hzy, hxy, hcz, hcx, hcy⟩

omit [DecidableEq G] in
/-- Forgetting the provenance gives the established global tail-heavy
pure-edge profile. -/
theorem MinimalSupportTransversalShiftTargetPurePairAt.tailHeavyPureEdge
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1))
    (hpure : MinimalSupportTransversalShiftTargetPurePairAt
      g h hno hmin b z) :
    WitnessTailHeavyPureEdge g h := by
  obtain ⟨x, e, hxz, hez, hex, _homit, heTwo, hshape⟩ := hpure
  exact ⟨minimalSupportPrivateWitness g h hmin
      (minimalSupportTransversalShiftTarget g hno hmin b),
    e.succ, z, x,
    minimalSupportPrivateWitness_isWitness g h hmin
      (minimalSupportTransversalShiftTarget g hno hmin b),
    hez, hex, Ne.symm hxz, hshape, e, by omega⟩

omit [DecidableEq G] in
/-- Provenance-preserving normalization of one heavy selected target. -/
theorem shiftHeavyTargetSource_threeOmissionsAt_or_purePairAt
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B)
    (hb : b ∈ minimalSupportTransversalShiftHeavyTargetSources
      g h hno hmin) :
    let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
    MinimalSupportTransversalShiftTargetThreeOmissionsAt
        g h hno hmin b z ∨
      MinimalSupportTransversalShiftTargetPurePairAt
        g h hno hmin b z := by
  classical
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let c := minimalSupportPrivateWitness g h hmin u
  let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
  have hc : Witness g h c :=
    minimalSupportPrivateWitness_isWitness g h hmin u
  have huHeavy : u ∈ minimalSupportPrivateTailHeavyVertices g h hmin :=
    (mem_minimalSupportTransversalShiftHeavyTargetSources_iff
      g h hno hmin b).mp hb
  obtain ⟨k, hk⟩ :=
    (mem_minimalSupportPrivateTailHeavyVertices_iff
      g h hmin u).mp huHeavy
  have hkC : 2 ≤ c k.succ := by
    simpa [c] using hk
  have hcz : c z = -1 := by
    simpa [c, u, z] using
      (minimalSupportTransversalShiftEdgeLabel_spec
        g hg hh hno hmin b).2.2
  have hkNotOmit : c k.succ ≠ -1 := by omega
  have hkUpper := witness_coeff_le_card_witnessOmissionCoordinates
    g hc hkNotOmit
  have htwoOmissions : 2 ≤ (witnessOmissionCoordinates c).card := by
    exact_mod_cast hkC.trans hkUpper
  have hzMem : z ∈ witnessOmissionCoordinates c := by
    simp [witnessOmissionCoordinates, hcz]
  have hxExists : ∃ x ∈ witnessOmissionCoordinates c, x ≠ z := by
    by_contra hnone
    have hsubset : witnessOmissionCoordinates c ⊆ {z} := by
      intro x hx
      simp only [Finset.mem_singleton]
      by_contra hxz
      exact hnone ⟨x, hx, hxz⟩
    have hcard := Finset.card_le_card hsubset
    have hone : (witnessOmissionCoordinates c).card ≤ 1 := by
      simpa using hcard
    omega
  obtain ⟨x, hxMem, hxz⟩ := hxExists
  have hcx : c x = -1 := by
    simpa [witnessOmissionCoordinates] using hxMem
  have hzx : z ≠ x := Ne.symm hxz
  by_cases hextra : ∃ y : Fin (m + 1),
      y ≠ z ∧ y ≠ x ∧ c y = -1
  · left
    obtain ⟨y, hyz, hyx, hcy⟩ := hextra
    exact ⟨x, y, hzx, Ne.symm hyz, Ne.symm hyx,
      hcz, hcx, hcy⟩
  · right
    have hexact : ∀ y, c y = -1 ↔ y = z ∨ y = x := by
      intro y
      constructor
      · intro hcy
        by_contra hy
        push Not at hy
        exact hextra ⟨y, hy.1, hy.2, hcy⟩
      · intro hy
        rcases hy with rfl | rfl
        · exact hcz
        · exact hcx
    have hkz : k.succ ≠ z := by
      intro hkz
      rw [hkz, hcz] at hkC
      omega
    have hkx : k.succ ≠ x := by
      intro hkx
      rw [hkx, hcx] at hkC
      omega
    have hkCases := witness_coeff_eq_zero_or_one_or_two_of_exact_pair
      g hc z x k.succ hzx hexact hkz hkx
    have hkTwo : c k.succ = 2 := by
      rcases hkCases with hkZero | hkOne | hkTwo <;> omega
    have hshape := exactPair_coeff_two_eq_pureEdgeCoeffs
      g hc z x k.succ hzx hexact hkz hkx hkTwo
    exact ⟨x, k, hxz, hkz, hkx, hexact, hkTwo, hshape⟩

/-- The provenance-rich global structural residual attached to a minimal
transversal. -/
def MinimalSupportTransversalHeavyTargetStructuralResidual
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B) : Prop :=
  ∃ b : ↥B,
    b ∈ minimalSupportTransversalShiftHeavyTargetSources g h hno hmin ∧
      let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
      MinimalSupportTransversalShiftTargetThreeOmissionsAt
          g h hno hmin b z ∨
        MinimalSupportTransversalShiftTargetPurePairAt
          g h hno hmin b z

omit [DecidableEq G] in
/-- The retained residual still implies the broad structural alternative. -/
theorem MinimalSupportTransversalHeavyTargetStructuralResidual.profiles
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (hres : MinimalSupportTransversalHeavyTargetStructuralResidual
      g hg hh hno hmin) :
    WitnessThreeDistinctOmissions g h ∨ WitnessTailHeavyPureEdge g h := by
  obtain ⟨b, _hb, hthree | hpure⟩ := hres
  · exact Or.inl
      (hthree.threeDistinct g hno hmin b
        (minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b))
  · exact Or.inr
      (hpure.tailHeavyPureEdge g hno hmin b
        (minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b))

/-- Critical endpoint retaining the exact target-private structural witness
instead of projecting immediately to a broad profile proposition. -/
theorem critical_largeCross_or_transversalHeavyTargetStructuralResidual
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (hno : ¬ ∃ e : Fin (n + 1), ∀ r : Fin (n + 1) → ℤ,
      Witness g ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) r → r e ≠ 0)
    {B : Finset (Fin (n + 1))}
    (hmin : MinimalWitnessSupportTransversal g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)) B)
    (hB : min (s + 1) (Nat.log 2 (n + 1)) - 1 + 2 ≤ B.card) :
    criticalHalfGap n s * criticalHalfGap n s ≤
        4 * criticalCanonicalCrossMass g ∨
      MinimalSupportTransversalHeavyTargetStructuralResidual
        g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin := by
  let h := ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q))
  rcases critical_largeCross_or_privateTailLightVertices_card_le_one
      hq g hg hmin hB with hlarge | hlight
  · exact Or.inl hlarge
  · right
    have hBnonempty : B.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨b, hb⟩ :=
      exists_shiftHeavyTargetSource_of_nonempty_of_light_card_le_one
        g hno hmin hBnonempty hlight
    refine ⟨b, hb, ?_⟩
    exact shiftHeavyTargetSource_threeOmissionsAt_or_purePairAt
      g hg (half_add_half (by rw [pow_succ]; ring)) hno hmin b hb

end MinModulus
