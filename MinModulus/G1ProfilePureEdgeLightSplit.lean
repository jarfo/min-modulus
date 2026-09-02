/-
# Local light/heavy split for exact-profile pure edges

Each exact zero-containing triangle profile displays a three-coordinate pure
half edge.  The crossing-star proof needs only that one edge to be tail-light.
If it is, reduction gives a canonical root of weight at least `2^(n-3)`; if
not, its coefficient-two center is a concrete non-anchor tail coordinate.
-/
import MinModulus.G1MinimalSupportLocalLight

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A tail-heavy witness whose entire coefficient vector is one pure edge. -/
def WitnessTailHeavyPureEdge
    (g : Fin (m + 1) → G) (h : G) : Prop :=
  ∃ c : Fin (m + 1) → ℤ, ∃ x a b : Fin (m + 1),
    Witness g h c ∧ x ≠ a ∧ x ≠ b ∧ a ≠ b ∧
      c = pureEdgeCoeffs x a b ∧
      ∃ k : Fin m, 2 ≤ c k.succ

omit [DecidableEq G] in
/-- The heavy tail coordinate of a pure edge is necessarily its
coefficient-two center. -/
theorem WitnessTailHeavyPureEdge.exists_center_tail
    {g : Fin (m + 1) → G} {h : G}
    (hpure : WitnessTailHeavyPureEdge g h) :
    ∃ c : Fin (m + 1) → ℤ, ∃ x a b : Fin (m + 1), ∃ k : Fin m,
      Witness g h c ∧ x ≠ a ∧ x ≠ b ∧ a ≠ b ∧
        c = pureEdgeCoeffs x a b ∧ x = k.succ ∧ c k.succ = 2 := by
  obtain ⟨c, x, a, b, hc, hxa, hxb, hab, hpure, k, hk⟩ := hpure
  have hxk : x = k.succ := by
    by_contra hxk
    have hkx : k.succ ≠ x := Ne.symm hxk
    rw [hpure] at hk
    by_cases hka : k.succ = a <;> by_cases hkb : k.succ = b <;>
      simp [pureEdgeCoeffs, hkx, hka, hkb, hab,
        Ne.symm hxa, Ne.symm hxb, Ne.symm hab] at hk
  refine ⟨c, x, a, b, k, hc, hxa, hxb, hab, hpure, hxk, ?_⟩
  subst x
  simp [hpure, pureEdgeCoeffs, hxa, hxb]

/-- A displayed exact-pair coefficient-two edge either supplies the desired
high-weight canonical root or is itself a structured tail-heavy pure edge. -/
theorem exists_exactPairTwo_pureEdgeCanonical_weight_or_tailHeavy
    (g : Fin (m + 1) → G)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    (a b x : Fin (m + 1)) (hab : a ≠ b)
    (homit : ∀ i, c i = -1 ↔ i = a ∨ i = b)
    (hxa : x ≠ a) (hxb : x ≠ b) (hcx : c x = 2) :
    (∃ r : ReducedSubsetSumCollision g h,
      r ∈ canonicalReducedCollisions (g := g) hh ∧
        2 ^ (m - 3) ≤ reducedCollisionWeight (m := m) r) ∨
      WitnessTailHeavyPureEdge g h := by
  by_cases hlight : ∀ k : Fin m, c k.succ ≤ 1
  · exact Or.inl (exists_exactPairTwo_pureEdgeCanonical_weight
      g hh hh0 hc a b x hab homit hxa hxb hcx hlight)
  · right
    push Not at hlight
    obtain ⟨k, hk⟩ := hlight
    have hpure : c = pureEdgeCoeffs x a b :=
      exactPair_coeff_two_eq_pureEdgeCoeffs
        g hc a b x hab homit hxa hxb hcx
    exact ⟨c, x, a, b, hc, hxa, hxb, hab, hpure, k, by omega⟩

/-- Local pure-edge split for the `(0,0,2)` exact profile. -/
theorem exists_zeroZeroTwo_pureEdgeCanonical_weight_or_tailHeavy
    (g : Fin (m + 1) → G)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hprofile : WitnessExactTriangleZeroZeroTwo g h) :
    (∃ r : ReducedSubsetSumCollision g h,
      r ∈ canonicalReducedCollisions (g := g) hh ∧
        2 ^ (m - 3) ≤ reducedCollisionWeight (m := m) r) ∨
      WitnessTailHeavyPureEdge g h := by
  obtain ⟨cAB, _cBD, _cDA, a, b, d, hcAB, _hcBD, _hcDA,
    hab, hbd, hda, hAB, _hBD, _hDA, hABd, _hBDa, _hDAb⟩ := hprofile
  exact exists_exactPairTwo_pureEdgeCanonical_weight_or_tailHeavy
    g hh hh0 hcAB a b d hab hAB hda (Ne.symm hbd) hABd

/-- Local pure-edge split for the all-zero exact profile. -/
theorem exists_allZero_pureEdgeCanonical_weight_or_tailHeavy
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hh0 : h ≠ 0)
    (hprofile : WitnessExactTriangleAllZero g h) :
    (∃ r : ReducedSubsetSumCollision g h,
      r ∈ canonicalReducedCollisions (g := g) hh ∧
        2 ^ (m - 3) ≤ reducedCollisionWeight (m := m) r) ∨
      WitnessTailHeavyPureEdge g h := by
  obtain ⟨cAB, cBD, cDA, a, b, d, hcAB, hcBD, hcDA,
    hab, hbd, hda, hAB, hBD, hDA, hABd, hBDa, hDAb⟩ := hprofile
  obtain ⟨x, _y, _z, hx, _hy, _hz, _hxy, _hyz, _hzx,
    hABx, _hBDy, _hDAz⟩ :=
    exists_six_distinct_pure_centers_of_triangle_all_zero
      g hg hh hcAB hcBD hcDA a b d hab hbd hda
        hAB hBD hDA hABd hBDa hDAb
  exact exists_exactPairTwo_pureEdgeCanonical_weight_or_tailHeavy
    g hh hh0 hcAB a b x hab hAB hx.1 hx.2.1 hABx

end MinModulus
