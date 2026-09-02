/-
# Localizing the global pure-edge star center

Outside the exact-triangle frontier, the complete family of pure
half-witness omission pairs has a common coordinate.  This file identifies
that coordinate in the operational transition geometry.

The old and new transition edges share exactly one endpoint, so the global
star center must be that shared endpoint.  Independently, the retained
target's owner/external geometry shows that the star center is either the
target owner or lies outside the minimal transversal.  These two facts make
the remaining star arm compatible with the protected owner and quarter-
escape data.
-/
import MinModulus.G1PrivateHeavyTargetPureEdgeFamily

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- In a center-changing transition, the common coordinate of the complete
pure-edge omission family is exactly the unique shared endpoint of the old
and new edges. -/
theorem MinimalSupportTransversalShiftTargetPureCenterChangeAt.exists_sharedEndpoint_eq_globalStarCenter
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1))
    (c : Fin (m + 1) → ℤ) (k : Fin m)
    (hchange : MinimalSupportTransversalShiftTargetPureCenterChangeAt
      g h hno hmin b z c k)
    (r : Fin (m + 1))
    (hstar : ∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P) :
    ∃ x y w : Fin (m + 1),
      (y = z ∨ y = x) ∧ y ≠ w ∧
      w ≠ z ∧ w ≠ x ∧
      ExactOmissions
        (minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b)) {z, x} ∧
      ExactOmissions c {y, w} ∧ r = y := by
  classical
  obtain ⟨x, e, y, w, hxz, _hez, _hex, homitP, heTwo,
    hyEndpoint, hyw, hwz, hwx, _hky, _hkw, homitC, hkTwo,
    _hkCenter⟩ := hchange.exists_freshEndpoint
      g hg hh hne hunique hno hmin b z c k
  have hp : Witness g h
      (minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b)) :=
    minimalSupportPrivateWitness_isWitness g h hmin
      (minimalSupportTransversalShiftTarget g hno hmin b)
  have hc : Witness g h c := by
    rcases hchange with ⟨_x, _e, _y, _w, _hxz, _hez, _hex,
      _homitP, _heTwo, _hpShape, _hyEndpoint, _hyw, _hky, _hkw,
      hc, _homitC, _hkTwo, _hcShape, _hkCenter⟩
    exact hc
  have hOldMem : {z, x} ∈ witnessPureEdgeOmissionPairs g h := by
    apply (mem_witnessPureEdgeOmissionPairs_iff g h {z, x}).2
    refine ⟨Finset.card_pair (Ne.symm hxz),
      minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b),
      e.succ, hp, ?_, heTwo⟩
    · intro a
      simpa using homitP a
  have hNewMem : {y, w} ∈ witnessPureEdgeOmissionPairs g h := by
    apply (mem_witnessPureEdgeOmissionPairs_iff g h {y, w}).2
    refine ⟨Finset.card_pair hyw, c, k.succ, hc, ?_, hkTwo⟩
    · intro a
      simpa using homitC a
  have hrOld : r = z ∨ r = x := by
    simpa using hstar {z, x} hOldMem
  have hrNew : r = y ∨ r = w := by
    simpa using hstar {y, w} hNewMem
  have hry : r = y := by
    rcases hrNew with hry | hrw
    · exact hry
    · rcases hrOld with hrz | hrx
      · exact False.elim (hwz (hrw.symm.trans hrz))
      · exact False.elim (hwx (hrw.symm.trans hrx))
  exact ⟨x, y, w, hyEndpoint, hyw, hwz, hwx,
    fun a ↦ by simpa using homitP a,
    fun a ↦ by simpa using homitC a, hry⟩

omit [DecidableEq G] in
/-- For a canonical retained pure target, a global pure-edge star center is
either the target owner or external to the minimal transversal. -/
theorem minimalSupportTransversalShiftTargetPurePair_globalStarCenter_owner_or_external
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B)
    (hpure : MinimalSupportTransversalShiftTargetPurePairAt
      g h hno hmin b
        (minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b))
    (r : Fin (m + 1))
    (hstar : ∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P) :
    r = (minimalSupportTransversalShiftTarget g hno hmin b :
      Fin (m + 1)) ∨ r ∉ B := by
  classical
  let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let p := minimalSupportPrivateWitness g h hmin u
  obtain ⟨x, e, hxz, _hez, _hex, homit, heTwo, _hshape,
      howner⟩ :=
    minimalSupportTransversalShiftTargetPurePair_owner_or_external
      g hg hh hno hmin b hpure
  have hp : Witness g h p :=
    minimalSupportPrivateWitness_isWitness g h hmin u
  have hPairMem : {z, x} ∈ witnessPureEdgeOmissionPairs g h := by
    apply (mem_witnessPureEdgeOmissionPairs_iff g h {z, x}).2
    refine ⟨Finset.card_pair (Ne.symm hxz), p, e.succ, hp, ?_, ?_⟩
    · intro a
      simpa [p, u, z] using homit a
    · simpa [p, u] using heTwo
  have hrEndpoints : r = z ∨ r = x := by
    simpa using hstar {z, x} hPairMem
  have hzB : z ∉ B :=
    (minimalSupportTransversalShiftEdgeLabel_spec
      g hg hh hno hmin b).1
  rcases howner with ⟨huCenter, hxB⟩ | ⟨huX, _heB⟩
  · rcases hrEndpoints with hrz | hrx
    · exact Or.inr (by simpa [hrz] using hzB)
    · exact Or.inr (by simpa [hrx] using hxB)
  · rcases hrEndpoints with hrz | hrx
    · exact Or.inr (by simpa [hrz] using hzB)
    · exact Or.inl (by simpa [u] using hrx.trans huX.symm)

omit [DecidableEq G] in
/-- Combined local endpoint for a center-changing canonical target: either
the complete pure-edge family supplies an exact omission triangle, or its
global star center is the transition's shared endpoint and is localized to
the target owner or outside the transversal. -/
theorem minimalSupportTransversalShiftTargetPureCenterChange_exactTriangle_or_globalStar
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (c : Fin (m + 1) → ℤ) (k : Fin m)
    (hchange : MinimalSupportTransversalShiftTargetPureCenterChangeAt
      g h hno hmin b
        (minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b) c k) :
    WitnessExactOmissionTriangle g h ∨
      ∃ r : Fin (m + 1),
        (∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P) ∧
        (r = (minimalSupportTransversalShiftTarget g hno hmin b :
            Fin (m + 1)) ∨ r ∉ B) ∧
        ∃ x y w : Fin (m + 1),
          (y = minimalSupportTransversalShiftEdgeLabel
              g hg hh hno hmin b ∨ y = x) ∧
          y ≠ w ∧
          w ≠ minimalSupportTransversalShiftEdgeLabel
            g hg hh hno hmin b ∧
          w ≠ x ∧
          ExactOmissions
            (minimalSupportPrivateWitness g h hmin
              (minimalSupportTransversalShiftTarget g hno hmin b))
            {minimalSupportTransversalShiftEdgeLabel
              g hg hh hno hmin b, x} ∧
          ExactOmissions c {y, w} ∧ r = y := by
  classical
  let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
  change MinimalSupportTransversalShiftTargetPureCenterChangeAt
    g h hno hmin b z c k at hchange
  have hpure : MinimalSupportTransversalShiftTargetPurePairAt
      g h hno hmin b z := by
    rcases hchange with ⟨x, e, _y, _w, hxz, hez, hex,
      homitP, heTwo, hpShape, _hyEndpoint, _hyw, _hky, _hkw,
      _hc, _homitC, _hkTwo, _hcShape, _hkCenter⟩
    exact ⟨x, e, hxz, hez, hex, homitP, heTwo, hpShape⟩
  have hp : Witness g h
      (minimalSupportPrivateWitness g h hmin
        (minimalSupportTransversalShiftTarget g hno hmin b)) :=
    minimalSupportPrivateWitness_isWitness g h hmin
      (minimalSupportTransversalShiftTarget g hno hmin b)
  have hF : (witnessPureEdgeOmissionPairs g h).Nonempty := by
    rcases hpure with ⟨x, e, hxz, _hez, _hex,
      homitP, heTwo, _hpShape⟩
    exact witnessPureEdgeOmissionPairs_nonempty_of_exactPairTwo
      g hp z x e.succ (Ne.symm hxz) homitP heTwo
  rcases witnessPureEdgeOmissionPairs_common_or_exactTriangle
      g hg hh hF with ⟨r, hstar⟩ | htriangle
  · right
    have hlocation :=
      minimalSupportTransversalShiftTargetPurePair_globalStarCenter_owner_or_external
        g hg hh hno hmin b (by simpa [z] using hpure) r hstar
    obtain ⟨x, y, w, hyEndpoint, hyw, hwz, hwx,
      homitP, homitC, hry⟩ :=
      hchange.exists_sharedEndpoint_eq_globalStarCenter
        g hg hh hne hunique hno hmin b z c k r hstar
    exact ⟨r, hstar, hlocation, x, y, w,
      by simpa [z] using hyEndpoint, hyw, by simpa [z] using hwz,
      hwx, by simpa [z] using homitP, homitC, hry⟩
  · exact Or.inl htriangle

end MinModulus
