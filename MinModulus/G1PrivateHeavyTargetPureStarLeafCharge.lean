/-
# The transition leaf carried by the canonical star-center avoider

The canonical witness vanishing at a global pure-edge star center is not an
arbitrary light witness.  Witness combination with the center-changing
payload forces it to omit the payload's other edge endpoint.  The protected
quarter escape cannot equal that endpoint, and privacy locates the endpoint
at the payload owner or outside the transversal.

After canonical reduction, the resulting collision has coefficient zero at
the star center and coefficient of absolute value one at this forced leaf.
This is the signed incidence needed to connect the global-star reduction to
the canonical crossing machinery.
-/
import MinModulus.G1PrivateHeavyTargetPureStarAvoider

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- The star-center avoiding witness must omit the non-center leaf of the
center-changing payload.  That leaf differs from the protected quarter
escape and is owner-or-external; it is external when the star is the owner. -/
theorem minimalSupportTransversalShiftTargetPureCenterChange_globalStar_avoiderLeaf
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ d : Fin (m + 1) → ℤ,
      Witness g h d → d a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B)
    (qv : Fin (m + 1) → ℤ) (hqv : Witness g t qv)
    (owner : ↥B) (c : Fin (m + 1) → ℤ)
    (hprivate : ∀ a ∈ B, a ≠ owner → c a = 0)
    (k : Fin m)
    (i : Fin (m + 1)) (hi : 2 * qv i + 2 ≤ c i)
    (hchange : MinimalSupportTransversalShiftTargetPureCenterChangeAt
      g h hno hmin b
        (minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b) c k)
    (r : Fin (m + 1))
    (hstar : ∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P) :
    ∃ w : Fin (m + 1),
      w ≠ r ∧ c w = -1 ∧ supportAvoidingWitnessAt g hno r w = -1 ∧
      i ≠ w ∧ (w = owner ∨ w ∉ B) ∧
      (r = (owner : Fin (m + 1)) → w ∉ B) := by
  classical
  let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
  change MinimalSupportTransversalShiftTargetPureCenterChangeAt
    g h hno hmin b z c k at hchange
  have hc : Witness g h c := by
    rcases hchange with ⟨_x, _e, _y, _w, _hxz, _hez, _hex,
      _homitP, _heTwo, _hpShape, _hyEndpoint, _hyw, _hky, _hkw,
      hc, _homitC, _hkTwo, _hcShape, _hkCenter⟩
    exact hc
  obtain ⟨_x, y, w, _hyEndpoint, hyw, _hwz, _hwx,
      _homitP, homitC, hry⟩ :=
    hchange.exists_sharedEndpoint_eq_globalStarCenter
      g hg hh hne hunique hno hmin b z c k r hstar
  have hcr : c r = -1 := by
    rw [hry]
    exact (homitC _).2 (by simp)
  have hcrNe : c r ≠ 0 := by omega
  obtain ⟨a, hca, haa⟩ := exists_common_omission_of_witness_ne_zero_zero
    g hg hh hc (supportAvoidingWitnessAt_isWitness g hno r)
      hcrNe (supportAvoidingWitnessAt_eq_zero g hno r)
  have haEndpoints : a = y ∨ a = w := by
    simpa using (homitC a).1 hca
  have haw : a = w := by
    rcases haEndpoints with hay | haw
    · have har : a = r := hay.trans hry.symm
      have harOmit : supportAvoidingWitnessAt g hno r r = -1 := by
        simpa [har] using haa
      rw [supportAvoidingWitnessAt_eq_zero g hno r] at harOmit
      omega
    · exact haw
  have hcw : c w = -1 := by simpa [haw] using hca
  have hawOmit : supportAvoidingWitnessAt g hno r w = -1 := by
    simpa [haw] using haa
  have hwr : w ≠ r := by
    intro hwr
    exact hyw (hry.symm.trans hwr.symm)
  have hiw : i ≠ w := by
    intro hiw
    have hi' : 2 * qv w + 2 ≤ c w := by simpa [hiw] using hi
    have hqFloor := hqv.2.1 w
    rw [hcw] at hi'
    omega
  have hwLocation : w = owner ∨ w ∉ B := by
    by_cases hwo : w = owner
    · exact Or.inl hwo
    · right
      intro hwB
      have hwZero := hprivate w hwB hwo
      omega
  have hwExternalOfOwner :
      r = (owner : Fin (m + 1)) → w ∉ B := by
    intro hrOwner hwB
    have hwo : w ≠ (owner : Fin (m + 1)) := by
      intro hwOwner
      exact hwr (hwOwner.trans hrOwner.symm)
    have hwZero := hprivate w hwB hwo
    omega
  exact ⟨w, hwr, hcw, hawOmit, hiw, hwLocation, hwExternalOfOwner⟩

/-- A canonical collision attached to the star outcome has zero coefficient
at the star center and signed unit coefficient at the forced transition
leaf.  All star/quarter location data is retained. -/
theorem MinimalSupportTransversalShiftTargetPureStarQuarterCanonicalOutcome.exists_canonicalLeaf
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ d : Fin (m + 1) → ℤ,
      Witness g h d → d a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B)
    (qv : Fin (m + 1) → ℤ) (hqv : Witness g t qv)
    (owner : ↥B) (c : Fin (m + 1) → ℤ)
    (hprivate : ∀ a ∈ B, a ≠ owner → c a = 0)
    (k : Fin m) (i : Fin (m + 1))
    (hi : 2 * qv i + 2 ≤ c i)
    (hchange : MinimalSupportTransversalShiftTargetPureCenterChangeAt
      g h hno hmin b
        (minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b) c k)
    (houtcome :
      MinimalSupportTransversalShiftTargetPureStarQuarterCanonicalOutcome
        g hh hno hmin b owner k i) :
    ∃ r : Fin (m + 1), ∃ q : ReducedSubsetSumCollision g h,
      ∃ w : Fin (m + 1),
        (∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P) ∧
        ((r = (minimalSupportTransversalShiftTarget g hno hmin b :
              Fin (m + 1)) ∧
            owner = minimalSupportTransversalShiftTarget g hno hmin b ∧
            k.succ ∉ B ∧ i ∉ B ∧ i ≠ r) ∨
          (r ∉ B ∧ i ≠ r ∧ (i = owner ∨ i ∉ B))) ∧
        q ∈ canonicalReducedCollisions (g := g) hh ∧
        w ≠ r ∧ c w = -1 ∧
        supportAvoidingWitnessAt g hno r w = -1 ∧
        i ≠ w ∧ (w = owner ∨ w ∉ B) ∧
        (r = (owner : Fin (m + 1)) → w ∉ B) ∧
        subsetCollisionCoeffs q.val.1 q.val.2 r = 0 ∧
        (subsetCollisionCoeffs q.val.1 q.val.2 w = -1 ∨
          subsetCollisionCoeffs q.val.1 q.val.2 w = 1) := by
  obtain ⟨r, hstar, hsplit, q, hqCanonical, hcoeff⟩ := houtcome
  obtain ⟨w, hwr, hcw, haw, hiw, hwLocation, hwExternal⟩ :=
    minimalSupportTransversalShiftTargetPureCenterChange_globalStar_avoiderLeaf
      g hg hh hne hunique hno hmin b qv hqv owner c hprivate k i hi
        hchange r hstar
  have hqr : subsetCollisionCoeffs q.val.1 q.val.2 r = 0 := by
    rcases hcoeff with hcoeff | hcoeff
    · rw [hcoeff]
      exact supportAvoidingWitnessAt_eq_zero g hno r
    · rw [hcoeff]
      simp [supportAvoidingWitnessAt_eq_zero g hno r]
  have hqw : subsetCollisionCoeffs q.val.1 q.val.2 w = -1 ∨
      subsetCollisionCoeffs q.val.1 q.val.2 w = 1 := by
    rcases hcoeff with hcoeff | hcoeff
    · exact Or.inl (by simpa [hcoeff] using haw)
    · right
      rw [hcoeff]
      simp [haw]
  exact ⟨r, q, w, hstar, hsplit, hqCanonical, hwr, hcw, haw,
    hiw, hwLocation, hwExternal, hqr, hqw⟩

end MinModulus
