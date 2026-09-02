/-
# Coupling the global pure-edge star to the protected quarter escape

The protected quarter gap cannot occur at an omitted coordinate of the
private-heavy payload: the quarter witness has coefficient floor `-1`, so
`2*q(i)+2 <= -1` is impossible.  In the exact-pure star arm this makes the
quarter escape different from the global star center.

If the star center is internal to the minimal transversal, target geometry
says that it is the target owner.  Since the payload also omits it, privacy
forces it to be the payload owner as well.  The payload's coefficient-two
center and the quarter escape are then both external.  If the star center is
external, it remains a second external coordinate distinct from the quarter
escape (which is still localized to the payload owner or outside `B`).
-/
import MinModulus.G1PrivateHeavyTargetPureStarCenter

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- Operational internal/external split for a global pure-edge star and the
protected quarter escape attached to a center-changing payload. -/
theorem minimalSupportTransversalShiftTargetPureCenterChange_globalStar_quarterSplit
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h t : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : G, u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B)
    (qv : Fin (m + 1) → ℤ) (hqv : Witness g t qv)
    (owner : ↥B) (c : Fin (m + 1) → ℤ)
    (hprivate : ∀ a ∈ B, a ≠ owner → c a = 0)
    (k : Fin m) (hk : 2 ≤ c k.succ)
    (hkLocation : k.succ = owner ∨ k.succ ∉ B)
    (i : Fin (m + 1)) (hi : 2 * qv i + 2 ≤ c i)
    (hiLocation : i = owner ∨ i ∉ B)
    (hchange : MinimalSupportTransversalShiftTargetPureCenterChangeAt
      g h hno hmin b
        (minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b) c k)
    (r : Fin (m + 1))
    (hstar : ∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P) :
    (r = (minimalSupportTransversalShiftTarget g hno hmin b :
          Fin (m + 1)) ∧
        owner = minimalSupportTransversalShiftTarget g hno hmin b ∧
        k.succ ∉ B ∧ i ∉ B ∧ i ≠ r) ∨
      (r ∉ B ∧ i ≠ r ∧ (i = owner ∨ i ∉ B)) := by
  classical
  let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  change MinimalSupportTransversalShiftTargetPureCenterChangeAt
    g h hno hmin b z c k at hchange
  have hpure : MinimalSupportTransversalShiftTargetPurePairAt
      g h hno hmin b z := by
    rcases hchange with ⟨x, e, _y, _w, hxz, hez, hex,
      homitP, heTwo, hpShape, _hyEndpoint, _hyw, _hky, _hkw,
      _hc, _homitC, _hkTwo, _hcShape, _hkCenter⟩
    exact ⟨x, e, hxz, hez, hex, homitP, heTwo, hpShape⟩
  obtain ⟨_x, _y, _w, _hyEndpoint, _hyw, _hwz, _hwx,
      _homitP, homitC, hry⟩ :=
    hchange.exists_sharedEndpoint_eq_globalStarCenter
      g hg hh hne hunique hno hmin b z c k r hstar
  have hcr : c r = -1 := by
    rw [hry]
    exact (homitC _).2 (by simp)
  have hiNeR : i ≠ r := by
    intro hir
    subst i
    have hqFloor := hqv.2.1 r
    rw [hcr] at hi
    omega
  have hlocation : r = (u : Fin (m + 1)) ∨ r ∉ B :=
    minimalSupportTransversalShiftTargetPurePair_globalStarCenter_owner_or_external
      g hg hh hno hmin b (by simpa [z] using hpure) r hstar
  rcases hlocation with hrU | hrExternal
  · left
    have hrB : r ∈ B := by
      rw [hrU]
      exact u.property
    have hownerR : (owner : Fin (m + 1)) = r := by
      by_contra hownerR
      have hzero := hprivate r hrB (Ne.symm hownerR)
      omega
    have hownerU : owner = u :=
      Subtype.ext (hownerR.trans hrU)
    have hkExternal : k.succ ∉ B := by
      rcases hkLocation with hkOwner | hkExternal
      · have hkR : k.succ = r := hkOwner.trans hownerR
        rw [hkR, hcr] at hk
        omega
      · exact hkExternal
    have hiExternal : i ∉ B := by
      rcases hiLocation with hiOwner | hiExternal
      · exact False.elim (hiNeR (hiOwner.trans hownerR))
      · exact hiExternal
    exact ⟨by simpa [u] using hrU, by simpa [u] using hownerU,
      hkExternal, hiExternal, hiNeR⟩
  · exact Or.inr ⟨hrExternal, hiNeR, hiLocation⟩

end MinModulus
