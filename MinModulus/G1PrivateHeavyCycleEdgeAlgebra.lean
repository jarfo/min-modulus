/-
# Pairwise-omission algebra on one private shift edge

For a canonical shift edge `b -> u`, write `c_b,c_u` for the private
witnesses at its endpoints and `r_b` for the avoiding witness at the source.
The pairs `(c_b,c_u)` and `(c_b,r_b)` have forced external common omissions.
If the target private witness is tail-heavy, `(c_u,r_b)` cannot be the exact-
negation arm of witness combination and therefore has a common omission too.

The three pair labels either coincide somewhere, giving one omission shared
by all three witnesses, or are pairwise distinct.  In the latter case each
witness has a known pair of omissions, so the existing exact-pair split gives
an exact omission triangle or a witness with three distinct omissions.
-/
import MinModulus.G1PrivateHeavyRootedStarCycle
import MinModulus.G1AvoidancePeriodThreeTriangle

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G]

/-- Three half-witnesses sharing one omitted coordinate. -/
def WitnessThreeSharedOmission
    (g : Fin m → G) (h : G) : Prop :=
  ∃ z : Fin m, ∃ c₀ c₁ c₂ : Fin m → ℤ,
    Witness g h c₀ ∧ Witness g h c₁ ∧ Witness g h c₂ ∧
      c₀ z = -1 ∧ c₁ z = -1 ∧ c₂ z = -1

/-- The three canonical witnesses attached to one private shift edge share
one omitted coordinate.  Unlike `WitnessThreeSharedOmission`, this retains
the source, target, and avoiding witnesses needed for edge-to-edge algebra. -/
def MinimalSupportPrivateShiftEdgeThreeSharedOmission
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) : Prop :=
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let cb := minimalSupportPrivateWitness g h hmin b
  let cu := minimalSupportPrivateWitness g h hmin u
  let rb := minimalSupportAvoidingWitness g hno b
  ∃ z : Fin (m + 1), cb z = -1 ∧ cu z = -1 ∧ rb z = -1

/-- The source-private and source-avoiding witnesses of every canonical
shift edge share an omission outside the transversal. -/
theorem exists_external_common_omission_private_avoiding_shiftEdge
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) :
    ∃ z : Fin (m + 1), z ∉ B ∧
      minimalSupportPrivateWitness g h hmin b z = -1 ∧
      minimalSupportAvoidingWitness g hno b z = -1 := by
  obtain ⟨z, hcbz, hrbz⟩ :=
    exists_common_omission_of_witness_ne_zero_zero
      g hg hh
      (minimalSupportPrivateWitness_isWitness g h hmin b)
      (minimalSupportAvoidingWitness_isWitness g hno b)
      (minimalSupportPrivateWitness_ne_zero g h hmin b)
      (minimalSupportAvoidingWitness_eq_zero g hno b)
  have hzB : z ∉ B := by
    intro hzB
    by_cases hzb : z = b
    · subst z
      have hrzero := minimalSupportAvoidingWitness_eq_zero g hno b
      omega
    · have hczero := minimalSupportPrivateWitness_eq_zero_of_ne
        g h hmin b hzB hzb
      omega
  exact ⟨z, hzB, hcbz, hrbz⟩

/-- The target-private and source-avoiding witnesses either share an
omission or are exact negatives. -/
theorem targetPrivate_avoiding_commonOmission_or_neg
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) :
    let u := minimalSupportTransversalShiftTarget g hno hmin b
    let cu := minimalSupportPrivateWitness g h hmin u
    let rb := minimalSupportAvoidingWitness g hno b
    (∃ z : Fin (m + 1), cu z = -1 ∧ rb z = -1) ∨ rb = -cu := by
  dsimp
  by_cases hcommon : ∃ z : Fin (m + 1),
      minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) z = -1 ∧
        minimalSupportAvoidingWitness g hno b z = -1
  · exact Or.inl hcommon
  · right
    apply witness_combination g hg hh
      (minimalSupportPrivateWitness_isWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b))
      (minimalSupportAvoidingWitness_isWitness g hno b)
    intro z hz
    exact hcommon ⟨z, hz⟩

/-- Tail-heaviness at the target excludes the exact-negation arm: the
avoiding witness still has coefficient floor `-1`. -/
theorem exists_common_omission_targetPrivate_avoiding_of_tailHeavy
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B)
    (huHeavy : minimalSupportTransversalShiftTarget g hno hmin b ∈
      minimalSupportPrivateTailHeavyVertices g h hmin) :
    let u := minimalSupportTransversalShiftTarget g hno hmin b
    let cu := minimalSupportPrivateWitness g h hmin u
    let rb := minimalSupportAvoidingWitness g hno b
    ∃ z : Fin (m + 1), cu z = -1 ∧ rb z = -1 := by
  dsimp
  rcases targetPrivate_avoiding_commonOmission_or_neg
      g hg hh hno hmin b with hcommon | hneg
  · exact hcommon
  · exfalso
    obtain ⟨k, hk⟩ :=
      (mem_minimalSupportPrivateTailHeavyVertices_iff
        g h hmin (minimalSupportTransversalShiftTarget g hno hmin b)).mp
        huHeavy
    have hfloor :=
      (minimalSupportAvoidingWitness_isWitness g hno b).2.1 k.succ
    have hcoeff := congrFun hneg k.succ
    simp only [Pi.neg_apply] at hcoeff
    omega

/-- A common omission of the target-private and source-avoiding witnesses is
either the target itself or lies outside the transversal. -/
theorem targetPrivate_avoiding_commonOmission_eq_target_or_external
    (g : Fin (m + 1) → G) {h : G}
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) {z : Fin (m + 1)}
    (hcu : minimalSupportPrivateWitness g h hmin
      (minimalSupportTransversalShiftTarget g hno hmin b) z = -1) :
    z = minimalSupportTransversalShiftTarget g hno hmin b ∨ z ∉ B := by
  by_cases hzu : z = minimalSupportTransversalShiftTarget g hno hmin b
  · exact Or.inl hzu
  · right
    intro hzB
    have hzero := minimalSupportPrivateWitness_eq_zero_of_ne
      g h hmin (minimalSupportTransversalShiftTarget g hno hmin b)
        hzB hzu
    omega

/-- A shift edge whose target private witness is tail-heavy carries three
half-witnesses with pairwise common omissions.  Those labels either have a
coincidence shared by all three witnesses, or reduce to the established
exact-triangle/three-distinct-omission frontier. -/
theorem tailHeavyTargetShiftEdge_threeSharedPackage_or_exactTriangle_or_threeDistinct
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B)
    (huHeavy : minimalSupportTransversalShiftTarget g hno hmin b ∈
      minimalSupportPrivateTailHeavyVertices g h hmin) :
    MinimalSupportPrivateShiftEdgeThreeSharedOmission g hno hmin b ∨
      WitnessExactOmissionTriangle g h ∨
      WitnessThreeDistinctOmissions g h := by
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let cb := minimalSupportPrivateWitness g h hmin b
  let cu := minimalSupportPrivateWitness g h hmin u
  let rb := minimalSupportAvoidingWitness g hno b
  obtain ⟨x, _hxB, hcbx, hrbx⟩ :=
    exists_external_common_omission_private_avoiding_shiftEdge
      g hg hh hno hmin b
  let y := minimalSupportPrivateCommonOmissionLabel g hg hh hmin
    (minimalSupportPrivateShiftCycleEdgePair
      g hno hmin b (d := 1) 0)
  have hySpec := minimalSupportPrivateCommonOmissionLabel_spec g hg hh hmin
    (minimalSupportPrivateShiftCycleEdgePair
      g hno hmin b (d := 1) 0)
  have hvertex : minimalSupportPrivateShiftCycleVertex
      g hno hmin b (0 : Fin 1) = b := by
    rfl
  have hycb : cb y = -1 := by
    simpa [y, cb, hvertex, minimalSupportPrivateShiftCycleEdgePair] using
      hySpec.2.1
  have hycu : cu y = -1 := by
    simpa [y, cu, u, hvertex,
      minimalSupportPrivateShiftCycleEdgePair] using hySpec.2.2
  obtain ⟨z, hcuz, hrbz⟩ :=
    exists_common_omission_targetPrivate_avoiding_of_tailHeavy
      g hg hh hno hmin b huHeavy
  by_cases hxy : x = y
  · left
    have hcux : cu x = -1 := by
      rw [hxy]
      exact hycu
    exact ⟨x, hcbx, hcux, hrbx⟩
  by_cases hyz : y = z
  · left
    subst z
    exact ⟨y, hycb, hycu, hrbz⟩
  by_cases hzx : z = x
  · left
    subst z
    exact ⟨x, hcbx, hcuz, hrbx⟩
  rcases exactPairOmissions_or_threeDistinctOmissions
      g (minimalSupportPrivateWitness_isWitness g h hmin b)
        hxy hcbx hycb with hcbExact | hthree
  · rcases exactPairOmissions_or_threeDistinctOmissions
        g (minimalSupportPrivateWitness_isWitness g h hmin u)
          hyz hycu hcuz with hcuExact | hthree
    · rcases exactPairOmissions_or_threeDistinctOmissions
          g (minimalSupportAvoidingWitness_isWitness g hno b)
            hzx hrbz hrbx with hrExact | hthree
      · exact Or.inr (Or.inl
          ⟨cb, cu, rb, x, y, z,
            minimalSupportPrivateWitness_isWitness g h hmin b,
            minimalSupportPrivateWitness_isWitness g h hmin u,
            minimalSupportAvoidingWitness_isWitness g hno b,
            hxy, hyz, hzx, hcbExact, hcuExact, by
              intro i
              simpa [or_comm] using hrExact i⟩)
      · exact Or.inr (Or.inr hthree)
    · exact Or.inr (Or.inr hthree)
  · exact Or.inr (Or.inr hthree)

/-- The fixed-edge package implies the ambient three-witness statement used
by the existing triangle frontier. -/
theorem tailHeavyTargetShiftEdge_threeShared_or_exactTriangle_or_threeDistinct
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ e : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r e ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B)
    (huHeavy : minimalSupportTransversalShiftTarget g hno hmin b ∈
      minimalSupportPrivateTailHeavyVertices g h hmin) :
    WitnessThreeSharedOmission g h ∨
      WitnessExactOmissionTriangle g h ∨
      WitnessThreeDistinctOmissions g h := by
  rcases
      tailHeavyTargetShiftEdge_threeSharedPackage_or_exactTriangle_or_threeDistinct
        g hg hh hno hmin b huHeavy with hshared | htriangle | hthree
  · left
    obtain ⟨z, hcbz, hcuz, hrbz⟩ := hshared
    exact ⟨z,
      minimalSupportPrivateWitness g h hmin b,
      minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b),
      minimalSupportAvoidingWitness g hno b,
      minimalSupportPrivateWitness_isWitness g h hmin b,
      minimalSupportPrivateWitness_isWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b),
      minimalSupportAvoidingWitness_isWitness g hno b,
      hcbz, hcuz, hrbz⟩
  · exact Or.inr (Or.inl htriangle)
  · exact Or.inr (Or.inr hthree)

end MinModulus
