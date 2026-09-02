/-
# Crossing or a fresh leaf from the opposite star avoider

Suppose a pure half-edge omits the global star center `r` and a leaf `w`.
The witness chosen to vanish at `w` must omit `r`.  If it is tail-light, its
canonical reduced collision differs from the canonical witness vanishing at
`r`, because their coefficients differ at `w`; the canonical crossing theorem
then gives an oriented crossing pair.  If it is tail-heavy, exact-pair
normalization yields three omissions or another pure edge `{r,x}` with a new
leaf `x != w`.

Thus failure of an immediate canonical crossing advances along genuinely
new leaves of the same global star rather than returning an unstructured
heavy witness.
-/
import MinModulus.G1PrivateHeavyTargetPureStarLeafCharge

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A new exact pure edge through the same star center, obtained from the
witness avoiding the preceding leaf. -/
def PureEdgeStarFreshLeafAt
    (g : Fin (m + 1) → G) (h : G)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ d : Fin (m + 1) → ℤ,
      Witness g h d → d a ≠ 0)
    (r w : Fin (m + 1)) : Prop :=
  ∃ x : Fin (m + 1), ∃ e : Fin m,
    x ≠ r ∧ x ≠ w ∧ e.succ ≠ r ∧ e.succ ≠ x ∧
      Witness g h (supportAvoidingWitnessAt g hno w) ∧
      ExactOmissions (supportAvoidingWitnessAt g hno w) {r, x} ∧
      supportAvoidingWitnessAt g hno w e.succ = 2 ∧
      supportAvoidingWitnessAt g hno w = pureEdgeCoeffs e.succ r x

/-- Avoiding the leaf of one pure star edge gives three omissions, an actual
canonical crossing with the center-avoider, or a new pure edge through the
same center with a different leaf. -/
theorem exactPureEdge_leafAvoider_threeOmissions_or_canonicalCross_or_freshLeaf
    (g : Fin (m + 1) → G) (hg : ValidTuple g)
    {h : G} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ a : Fin (m + 1), ∀ d : Fin (m + 1) → ℤ,
      Witness g h d → d a ≠ 0)
    (r w : Fin (m + 1))
    {c : Fin (m + 1) → ℤ} (hc : Witness g h c)
    (homit : ExactOmissions c {r, w})
    (q : ReducedSubsetSumCollision g h)
    (hqCanonical : q ∈ canonicalReducedCollisions (g := g) hh)
    (hqw : subsetCollisionCoeffs q.val.1 q.val.2 w = -1 ∨
      subsetCollisionCoeffs q.val.1 q.val.2 w = 1) :
    WitnessThreeDistinctOmissions g h ∨
      (∃ q' : ReducedSubsetSumCollision g h,
        (q, q') ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∨
          (q', q) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh) ∨
      PureEdgeStarFreshLeafAt g h hno r w := by
  classical
  let d := supportAvoidingWitnessAt g hno w
  have hd : Witness g h d := supportAvoidingWitnessAt_isWitness g hno w
  have hdw : d w = 0 := supportAvoidingWitnessAt_eq_zero g hno w
  have hcw : c w = -1 := (homit w).2 (by simp)
  obtain ⟨a, hca, hda⟩ := exists_common_omission_of_witness_ne_zero_zero
    g hg hh hc hd (by omega : c w ≠ 0) hdw
  have haEndpoints : a = r ∨ a = w := by
    simpa using (homit a).1 hca
  have har : a = r := by
    rcases haEndpoints with har | haw
    · exact har
    · have hdwOmit : d w = -1 := by simpa [haw] using hda
      rw [hdw] at hdwOmit
      omega
  have hdr : d r = -1 := by simpa [har] using hda
  by_cases hlight : ∀ k : Fin m, d k.succ ≤ 1
  · obtain ⟨q', hq'Canonical, hq'coeff⟩ :=
      exists_canonicalReducedCollision_coeff_eq_or_neg_of_tail_light
        g hh hne hd hlight
    have hq'Mem : q' ∈ canonicalReducedCollisions (g := g) hh :=
      (mem_canonicalReducedCollisions_iff).2 hq'Canonical
    have hq'w : subsetCollisionCoeffs q'.val.1 q'.val.2 w = 0 := by
      rcases hq'coeff with hq'coeff | hq'coeff
      · rw [hq'coeff]
        exact hdw
      · rw [hq'coeff]
        simp [hdw]
    have hq'Ne : q' ≠ q := by
      intro hq'eq
      have heq := congrArg
        (fun u : ReducedSubsetSumCollision g h ↦
          subsetCollisionCoeffs u.val.1 u.val.2 w) hq'eq
      rw [hq'w] at heq
      rcases hqw with hqw | hqw <;> omega
    have hcross := distinct_canonicalReducedCollisions_positive_negative_cross
      g hg hh hne q q'
        (mem_canonicalReducedCollisions_iff.mp hqCanonical)
        hq'Canonical hq'Ne
    right; left
    refine ⟨q', ?_⟩
    rcases hcross with hforward | hreverse
    · exact Or.inl ((mem_canonicalPositiveNegativeCrossPairs_iff).2
        ⟨hqCanonical, hq'Mem, Ne.symm hq'Ne, hforward⟩)
    · exact Or.inr ((mem_canonicalPositiveNegativeCrossPairs_iff).2
        ⟨hq'Mem, hqCanonical, hq'Ne, hreverse⟩)
  · push Not at hlight
    obtain ⟨e, he⟩ := hlight
    have heTwo : 2 ≤ d e.succ := by omega
    rcases tailHeavyWitness_threeDistinctOmissions_or_exactPureEdgeAt_of_omits
        g hd r hdr e heTwo with
      hthree | ⟨x, hrx, her, hex, homitD, heEqTwo, hshape⟩
    · exact Or.inl hthree
    · right; right
      have hxw : x ≠ w := by
        intro hxw
        have hdwOmit : d w = -1 := (homitD w).2 (Or.inr hxw.symm)
        rw [hdw] at hdwOmit
        omega
      exact ⟨x, e, hrx.symm, hxw, her, hex, hd,
        fun a ↦ by simpa using homitD a, heEqTwo, hshape⟩

/-- Apply the crossing-or-fresh-leaf transition to the actual protected
center-changing star outcome.  In the fresh-leaf arm the original canonical
root and all star/quarter location data remain available. -/
theorem MinimalSupportTransversalShiftTargetPureStarQuarterCanonicalOutcome.threeOmissions_or_canonicalCross_or_freshLeaf
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
    WitnessThreeDistinctOmissions g h ∨
      (∃ q q' : ReducedSubsetSumCollision g h,
        (q, q') ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∨
          (q', q) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh) ∨
      ∃ r : Fin (m + 1), ∃ q : ReducedSubsetSumCollision g h,
        ∃ w : Fin (m + 1),
          (∀ P ∈ witnessPureEdgeOmissionPairs g h, r ∈ P) ∧
          ((r = (minimalSupportTransversalShiftTarget g hno hmin b :
                Fin (m + 1)) ∧
              owner = minimalSupportTransversalShiftTarget g hno hmin b ∧
              k.succ ∉ B ∧ i ∉ B ∧ i ≠ r) ∨
            (r ∉ B ∧ i ≠ r ∧ (i = owner ∨ i ∉ B))) ∧
          q ∈ canonicalReducedCollisions (g := g) hh ∧
          w ≠ r ∧ i ≠ w ∧ (w = owner ∨ w ∉ B) ∧
          (r = (owner : Fin (m + 1)) → w ∉ B) ∧
          subsetCollisionCoeffs q.val.1 q.val.2 r = 0 ∧
          (subsetCollisionCoeffs q.val.1 q.val.2 w = -1 ∨
            subsetCollisionCoeffs q.val.1 q.val.2 w = 1) ∧
          PureEdgeStarFreshLeafAt g h hno r w := by
  obtain ⟨r, q, w, hstar, hsplit, hqCanonical, hwr, hcw, _haw,
      hiw, hwLocation, hwExternal, hqr, hqw⟩ :=
    houtcome.exists_canonicalLeaf g hg hh hne hunique hno hmin b qv hqv
      owner c hprivate k i hi hchange
  let z := minimalSupportTransversalShiftEdgeLabel g hg hh hno hmin b
  have hc : Witness g h c := by
    rcases hchange with ⟨_x, _e, _y, _w, _hxz, _hez, _hex,
      _homitP, _heTwo, _hpShape, _hyEndpoint, _hyw, _hky, _hkw,
      hc, _homitC, _hkTwo, _hcShape, _hkCenter⟩
    exact hc
  obtain ⟨_x, y, w₀, _hyEndpoint, _hyw₀, _hw₀z, _hw₀x,
      _homitP, homitC, hry⟩ :=
    hchange.exists_sharedEndpoint_eq_globalStarCenter
      g hg hh hne hunique hno hmin b z c k r hstar
  have hwEndpoints : w = y ∨ w = w₀ := by
    simpa using (homitC w).1 hcw
  have hww₀ : w = w₀ := by
    rcases hwEndpoints with hwy | hww₀
    · exact False.elim (hwr (hwy.trans hry.symm))
    · exact hww₀
  have homitRW : ExactOmissions c {r, w} := by
    intro a
    simpa [hry, hww₀] using homitC a
  rcases exactPureEdge_leafAvoider_threeOmissions_or_canonicalCross_or_freshLeaf
      g hg hh hne hno r w hc homitRW q hqCanonical hqw with
    hthree | hcross | hfresh
  · exact Or.inl hthree
  · obtain ⟨q', hcross⟩ := hcross
    exact Or.inr (Or.inl ⟨q, q', hcross⟩)
  · exact Or.inr (Or.inr ⟨r, q, w, hstar, hsplit, hqCanonical,
      hwr, hiw, hwLocation, hwExternal, hqr, hqw, hfresh⟩)

end MinModulus
