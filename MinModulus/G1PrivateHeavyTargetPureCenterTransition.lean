/-
# Turning pure-target center drop into a center-changing edge

The center-drop residual can be sharpened without any counting.  Every
witness must share an omission with a pure target: otherwise witness
combination makes the target the negative of that witness, contradicting the
witness floor at the target's coefficient-two center.

Apply this fact to the retained private-heavy witness.  Its shared pure
endpoint is a specified omission, while its heavy tail coordinate supplies
at least two omissions in total.  A third omission is already a structural
escape.  With exactly two omissions, the heavy witness is itself a pure edge;
the preceding center-drop theorem says that its center differs from the
target center.  This is the first genuine transition in the normalized pure
arm rather than merely a pair of coefficient inequalities.
-/
import MinModulus.G1PrivateHeavyTargetPureNormalizedResidual

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

omit [DecidableEq G] in
/-- Every witness shares an omitted endpoint with a nondegenerate pure-edge
witness.  Otherwise combination would make the pure edge its negative, which
has coefficient `-2` at the pure center and violates the witness floor. -/
theorem witness_exists_shared_pureEdge_endpoint
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) {c p : Fin (m + 1) → ℤ}
    (hc : Witness g h c) (hp : Witness g h p)
    (z x e : Fin (m + 1))
    (homit : ∀ a, p a = -1 ↔ a = z ∨ a = x)
    (heTwo : p e = 2) :
    ∃ y : Fin (m + 1),
      (y = z ∨ y = x) ∧ c y = -1 ∧ p y = -1 := by
  by_cases hshared : ∃ y, c y = -1 ∧ p y = -1
  · obtain ⟨y, hcy, hpy⟩ := hshared
    exact ⟨y, (homit y).mp hpy, hcy, hpy⟩
  · have hdisjoint : ∀ y, ¬(c y = -1 ∧ p y = -1) := by
      intro y hy
      exact hshared ⟨y, hy⟩
    have hneg : p = -c := witness_combination g hg hh hc hp hdisjoint
    have hcenter := congrFun hneg e
    have hcFloor := hc.2.1 e
    simp only [Pi.neg_apply] at hcenter
    omega

omit [DecidableEq G] in
/-- Retain both the specified omission and the actual heavy center while
normalizing a tail-heavy witness. -/
theorem tailHeavyWitness_threeDistinctOmissions_or_exactPureEdgeAt_of_omits
    (g : Fin (m + 1) → G) {h : G} {c : Fin (m + 1) → ℤ}
    (hc : Witness g h c) (y : Fin (m + 1)) (hcy : c y = -1)
    (k : Fin m) (hk : 2 ≤ c k.succ) :
    WitnessThreeDistinctOmissions g h ∨
      ∃ w : Fin (m + 1),
        y ≠ w ∧ k.succ ≠ y ∧ k.succ ≠ w ∧
        (∀ a, c a = -1 ↔ a = y ∨ a = w) ∧
        c k.succ = 2 ∧ c = pureEdgeCoeffs k.succ y w := by
  classical
  have hnotOmit : c k.succ ≠ -1 := by omega
  have hupper := witness_coeff_le_card_witnessOmissionCoordinates
    g hc hnotOmit
  have htwoOmissions : 2 ≤ (witnessOmissionCoordinates c).card := by
    exact_mod_cast hk.trans hupper
  have hyMem : y ∈ witnessOmissionCoordinates c := by
    simp [witnessOmissionCoordinates, hcy]
  have hwExists : ∃ w ∈ witnessOmissionCoordinates c, w ≠ y := by
    by_contra hnone
    have hsubset : witnessOmissionCoordinates c ⊆ {y} := by
      intro w hw
      simp only [Finset.mem_singleton]
      by_contra hwy
      exact hnone ⟨w, hw, hwy⟩
    have hcard := Finset.card_le_card hsubset
    have hone : (witnessOmissionCoordinates c).card ≤ 1 := by
      simpa using hcard
    omega
  obtain ⟨w, hwMem, hwy⟩ := hwExists
  have hcw : c w = -1 := by
    simpa [witnessOmissionCoordinates] using hwMem
  have hyw : y ≠ w := Ne.symm hwy
  rcases exactPairOmissions_or_threeDistinctOmissions
      g hc hyw hcy hcw with hexact | hthree
  · have hky : k.succ ≠ y := by
      intro hky
      rw [hky, hcy] at hk
      omega
    have hkw : k.succ ≠ w := by
      intro hkw
      rw [hkw, hcw] at hk
      omega
    have hkCases := witness_coeff_eq_zero_or_one_or_two_of_exact_pair
      g hc y w k.succ hyw hexact hky hkw
    have hkTwo : c k.succ = 2 := by
      rcases hkCases with hkZero | hkOne | hkTwo <;> omega
    have hshape := exactPair_coeff_two_eq_pureEdgeCoeffs
      g hc y w k.succ hyw hexact hky hkw hkTwo
    exact Or.inr ⟨w, hyw, hky, hkw, hexact, hkTwo, hshape⟩
  · exact Or.inl hthree

/-- A retained pure target and a second pure edge whose center is genuinely
different.  The new edge keeps an endpoint shared with the old target. -/
def MinimalSupportTransversalShiftTargetPureCenterChangeAt
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1))
    (c : Fin (m + 1) → ℤ) (k : Fin m) : Prop :=
  ∃ x : Fin (m + 1), ∃ e : Fin m,
    ∃ y w : Fin (m + 1),
      x ≠ z ∧ e.succ ≠ z ∧ e.succ ≠ x ∧
      (∀ a, minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) a = -1 ↔
        a = z ∨ a = x) ∧
      minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) e.succ = 2 ∧
      minimalSupportPrivateWitness g h hmin
          (minimalSupportTransversalShiftTarget g hno hmin b) =
        pureEdgeCoeffs e.succ z x ∧
      (y = z ∨ y = x) ∧ y ≠ w ∧
      k.succ ≠ y ∧ k.succ ≠ w ∧
      Witness g h c ∧
      (∀ a, c a = -1 ↔ a = y ∨ a = w) ∧
      c k.succ = 2 ∧ c = pureEdgeCoeffs k.succ y w ∧
      k.succ ≠ e.succ

omit [DecidableEq G] in
/-- A protected private-heavy witness distinct from a pure target either has
three omissions or is a new pure edge with a different center and an endpoint
shared with the target. -/
theorem minimalSupportTransversalShiftTargetPurePair_distinctPrivateHeavy_threeOmissions_or_centerChange
    (g : Fin (m + 1) → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ r : Fin (m + 1) → ℤ,
      Witness g h r → r a ≠ 0)
    {B : Finset (Fin (m + 1))}
    (hmin : MinimalWitnessSupportTransversal g h B)
    (b : ↥B) (z : Fin (m + 1))
    (hpure : MinimalSupportTransversalShiftTargetPurePairAt
      g h hno hmin b z)
    (owner : ↥B) (c : Fin (m + 1) → ℤ)
    (hc : Witness g h c)
    (hprivate : ∀ a ∈ B, a ≠ owner → c a = 0)
    (k : Fin m) (hk : 2 ≤ c k.succ)
    (hkLocation : k.succ = owner ∨ k.succ ∉ B)
    (hne : c ≠ minimalSupportPrivateWitness g h hmin
      (minimalSupportTransversalShiftTarget g hno hmin b)) :
    WitnessThreeDistinctOmissions g h ∨
      MinimalSupportTransversalShiftTargetPureCenterChangeAt
        g h hno hmin b z c k := by
  let u := minimalSupportTransversalShiftTarget g hno hmin b
  let p := minimalSupportPrivateWitness g h hmin u
  have hp : Witness g h p :=
    minimalSupportPrivateWitness_isWitness g h hmin u
  obtain ⟨x, e, _j, hxz, hez, hex, homit, heTwo, hshape,
      _hcenterCases, hkCenter, _hreverse, _hjCenter, _hjLocation,
      _hownerCenter⟩ :=
    minimalSupportTransversalShiftTargetPurePair_distinctPrivateHeavy
      g hg hno hmin b z hpure owner c hc hprivate k hk hkLocation hne
  have homitP : ∀ a, p a = -1 ↔ a = z ∨ a = x := by
    simpa [p, u] using homit
  have heTwoP : p e.succ = 2 := by
    simpa [p, u] using heTwo
  obtain ⟨y, hyEndpoint, hcy, _hpy⟩ :=
    witness_exists_shared_pureEdge_endpoint
      g hg hh hc hp z x e.succ homitP heTwoP
  rcases tailHeavyWitness_threeDistinctOmissions_or_exactPureEdgeAt_of_omits
      g hc y hcy k hk with hthree | ⟨w, hyw, hky, hkw,
        hexact, hkTwo, hcShape⟩
  · exact Or.inl hthree
  · right
    exact ⟨x, e, y, w, hxz, hez, hex, homit, heTwo, hshape,
      hyEndpoint, hyw, hky, hkw, hc, hexact, hkTwo, hcShape, hkCenter⟩

end MinModulus
