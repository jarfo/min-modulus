/-
# Fifth-stratum transition rigidity

At the fifth stratum, minimality restricts every nonzero bounded kernel
coefficient to magnitude `16` or `32`.  An internal difference of two
five-weight transition coefficients is at most `18`, so its only possible
nonzero magnitude is `16`.  Exact five-weight arithmetic then leaves two
unordered transition-level pairs, `{-8,8}` and `{-6,10}`.  Neither pair can
label three consecutive available edges of the punctured doubling cycle.
-/
import MinModulus.G1OddPrimaryFullCycleExactDivisorDescent

namespace MinModulus

variable {G : Type*} [AddCommGroup G]

/-- Exact arithmetic classification of an internal five-weight transition
gap of magnitude `16`.  This is the lower-stratum analogue of the existing
four-pattern boundary classification at magnitude `32`. -/
theorem fiveWeight_transitionDifference_natAbs_eq_sixteen
    (u v a b : ℤ)
    (hu : u ∈ twoRetainedNormalizedWeightLevels)
    (hv : v ∈ twoRetainedNormalizedWeightLevels)
    (ha : a ∈ twoRetainedNormalizedWeightLevels)
    (hb : b ∈ twoRetainedNormalizedWeightLevels)
    (habs : ((v - 2 * u) - (b - 2 * a)).natAbs = 16) :
    ((v - 2 * u = -8 ∧ b - 2 * a = 8) ∨
     (v - 2 * u = -6 ∧ b - 2 * a = 10) ∨
     (v - 2 * u = 8 ∧ b - 2 * a = -8) ∨
     (v - 2 * u = 10 ∧ b - 2 * a = -6)) := by
  simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
    Finset.mem_singleton] at hu hv ha hb
  rcases hu with rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl <;>
      rcases ha with rfl | rfl | rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num at habs <;> norm_num

/-- Three consecutive integer transitions from the pair `{-8,8}` cannot
stay in the five-weight interval when the initial value is an actual
five-weight level. -/
theorem fiveWeight_no_three_transitions_negEight_eight
    (u₀ u₁ u₂ u₃ : ℤ)
    (hu₀ : u₀ ∈ twoRetainedNormalizedWeightLevels)
    (hu₁ : -4 ≤ u₁) (hu₁' : u₁ ≤ 2)
    (hu₂ : -4 ≤ u₂) (hu₂' : u₂ ≤ 2)
    (hu₃ : -4 ≤ u₃) (hu₃' : u₃ ≤ 2)
    (h₀ : u₁ - 2 * u₀ = -8 ∨ u₁ - 2 * u₀ = 8)
    (h₁ : u₂ - 2 * u₁ = -8 ∨ u₂ - 2 * u₁ = 8)
    (h₂ : u₃ - 2 * u₂ = -8 ∨ u₃ - 2 * u₂ = 8) :
    False := by
  simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
    Finset.mem_singleton] at hu₀
  rcases hu₀ with rfl | rfl | rfl | rfl | rfl <;>
    rcases h₀ with h₀ | h₀ <;>
      rcases h₁ with h₁ | h₁ <;>
        rcases h₂ with h₂ | h₂ <;> omega

/-- Three consecutive integer transitions from the pair `{-6,10}` cannot
stay in the five-weight interval when the initial value is an actual
five-weight level. -/
theorem fiveWeight_no_three_transitions_negSix_ten
    (u₀ u₁ u₂ u₃ : ℤ)
    (hu₀ : u₀ ∈ twoRetainedNormalizedWeightLevels)
    (hu₁ : -4 ≤ u₁) (hu₁' : u₁ ≤ 2)
    (hu₂ : -4 ≤ u₂) (hu₂' : u₂ ≤ 2)
    (hu₃ : -4 ≤ u₃) (hu₃' : u₃ ≤ 2)
    (h₀ : u₁ - 2 * u₀ = -6 ∨ u₁ - 2 * u₀ = 10)
    (h₁ : u₂ - 2 * u₁ = -6 ∨ u₂ - 2 * u₁ = 10)
    (h₂ : u₃ - 2 * u₂ = -6 ∨ u₃ - 2 * u₂ = 10) :
    False := by
  simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
    Finset.mem_singleton] at hu₀
  rcases hu₀ with rfl | rfl | rfl | rfl | rfl <;>
    rcases h₀ with h₀ | h₀ <;>
      rcases h₁ with h₁ | h₁ <;>
        rcases h₂ with h₂ | h₂ <;> omega

/-- If every nonzero bounded multiple of the retained difference has
magnitude `16` or `32`, a nonconstant family of available transition
coefficients forces the punctured permutation to return after at most four
steps.  The proof is structural: all transition levels collapse to one of
the two exact pairs `{-8,8}` or `{-6,10}`, and three consecutive available
edges are arithmetically impossible.

The other arm retains the common transition coefficient for use by the
punctured-boundary relation; no boundary information is discarded. -/
theorem fiveWeightPuncturedPermutation_sixteenOrThirtyTwo_shortReturn_or_transition_constant
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p : ι) (hp : R p ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta C : G) (H : AddSubgroup G)
    (htransition : ∀ i, i ≠ p → R i ≠ p →
      (weight (R i) - 2 * weight i) • delta + C ∈ H)
    (hkernel1632 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • delta ∈ H → e.natAbs = 16 ∨ e.natAbs = 32) :
    (R (R p) = p ∨ R (R (R p)) = p ∨ R (R (R (R p))) = p) ∨
      ∀ i, i ≠ p → R i ≠ p →
        ∀ j, j ≠ p → R j ≠ p →
          weight (R i) - 2 * weight i =
            weight (R j) - 2 * weight j := by
  classical
  by_cases hall : ∀ i, i ≠ p → R i ≠ p →
      ∀ j, j ≠ p → R j ≠ p →
        weight (R i) - 2 * weight i =
          weight (R j) - 2 * weight j
  · exact Or.inr hall
  · push Not at hall
    obtain ⟨i, hi, hRi, j, hj, hRj, hij⟩ := hall
    let qi : ℤ := weight (R i) - 2 * weight i
    let qj : ℤ := weight (R j) - 2 * weight j
    have hiBounds := twoRetainedNormalizedWeight_bounds (hweight i hi)
    have hRiBounds :=
      twoRetainedNormalizedWeight_bounds (hweight (R i) hRi)
    have hjBounds := twoRetainedNormalizedWeight_bounds (hweight j hj)
    have hRjBounds :=
      twoRetainedNormalizedWeight_bounds (hweight (R j) hRj)
    have hqijMem : (qi - qj) • delta ∈ H := by
      have hsub := H.sub_mem (htransition i hi hRi) (htransition j hj hRj)
      convert hsub using 1
      dsimp only [qi, qj]
      module
    have hqijNe : qi - qj ≠ 0 := by
      dsimp only [qi, qj]
      exact sub_ne_zero.mpr hij
    have hqijAbs : (qi - qj).natAbs = 16 := by
      rcases hkernel1632 (qi - qj) hqijNe (by
          dsimp only [qi, qj]
          omega) (by
          dsimp only [qi, qj]
          omega) hqijMem with h16 | h32
      · exact h16
      · have h32Z : ((qi - qj).natAbs : ℤ) = 32 := by
          exact_mod_cast h32
        rcases Int.natAbs_eq (qi - qj) with hpos | hneg <;> omega
    have hfixed := fiveWeight_transitionDifference_natAbs_eq_sixteen
      (weight i) (weight (R i)) (weight j) (weight (R j))
        (hweight i hi) (hweight (R i) hRi)
        (hweight j hj) (hweight (R j) hRj) (by
          simpa only [qi, qj] using hqijAbs)
    have hlevel : ∀ k, k ≠ p → R k ≠ p →
        weight (R k) - 2 * weight k = qi ∨
          weight (R k) - 2 * weight k = qj := by
      intro k hk hRk
      let qk : ℤ := weight (R k) - 2 * weight k
      by_cases hki : qk = qi
      · exact Or.inl hki
      · have hkBounds := twoRetainedNormalizedWeight_bounds (hweight k hk)
        have hRkBounds :=
          twoRetainedNormalizedWeight_bounds (hweight (R k) hRk)
        have hdiffMem : (qk - qi) • delta ∈ H := by
          have hsub := H.sub_mem (htransition k hk hRk) (htransition i hi hRi)
          convert hsub using 1
          dsimp only [qk, qi]
          module
        have hdiffNe : qk - qi ≠ 0 := sub_ne_zero.mpr hki
        rcases hkernel1632 (qk - qi) hdiffNe (by
            dsimp only [qk, qi]
            omega) (by
            dsimp only [qk, qi]
            omega) hdiffMem with h16 | h32
        · right
          have h16Z : ((qk - qi).natAbs : ℤ) = 16 := by
            exact_mod_cast h16
          rcases Int.natAbs_eq (qk - qi) with hpos | hneg <;>
            rcases hfixed with hfixed | hfixed | hfixed | hfixed <;>
              rcases hfixed with ⟨hqi, hqj⟩ <;>
                dsimp only [qk, qi, qj] at hki ⊢ <;> omega
        · have h32Z : ((qk - qi).natAbs : ℤ) = 32 := by
            exact_mod_cast h32
          rcases Int.natAbs_eq (qk - qi) with hpos | hneg <;>
            dsimp only [qk, qi] at hki ⊢ <;> omega
    have hnoThree : ∀ k, k ≠ p → R k ≠ p →
        R (R k) ≠ p → R (R (R k)) ≠ p → False := by
      intro k hk hRk hRRk hRRRk
      have hkWeight := hweight k hk
      have hkBounds := twoRetainedNormalizedWeight_bounds (hweight k hk)
      have hRkBounds :=
        twoRetainedNormalizedWeight_bounds (hweight (R k) hRk)
      have hRRkBounds :=
        twoRetainedNormalizedWeight_bounds (hweight (R (R k)) hRRk)
      have hRRRkBounds :=
        twoRetainedNormalizedWeight_bounds (hweight (R (R (R k))) hRRRk)
      have hq0 := hlevel k hk hRk
      have hq1 := hlevel (R k) hRk hRRk
      have hq2 := hlevel (R (R k)) hRRk hRRRk
      rcases hfixed with hfixed | hfixed | hfixed | hfixed
      · rcases hfixed with ⟨hqi, hqj⟩
        apply fiveWeight_no_three_transitions_negEight_eight
          (weight k) (weight (R k)) (weight (R (R k)))
            (weight (R (R (R k)))) hkWeight hRkBounds.1 hRkBounds.2
              hRRkBounds.1 hRRkBounds.2 hRRRkBounds.1 hRRRkBounds.2
        all_goals
          rcases hq0 with hq0 | hq0 <;>
            rcases hq1 with hq1 | hq1 <;>
              rcases hq2 with hq2 | hq2 <;>
                dsimp only [qi, qj] at hqi hqj hq0 hq1 hq2 ⊢ <;> omega
      · rcases hfixed with ⟨hqi, hqj⟩
        apply fiveWeight_no_three_transitions_negSix_ten
          (weight k) (weight (R k)) (weight (R (R k)))
            (weight (R (R (R k)))) hkWeight hRkBounds.1 hRkBounds.2
              hRRkBounds.1 hRRkBounds.2 hRRRkBounds.1 hRRRkBounds.2
        all_goals
          rcases hq0 with hq0 | hq0 <;>
            rcases hq1 with hq1 | hq1 <;>
              rcases hq2 with hq2 | hq2 <;>
                dsimp only [qi, qj] at hqi hqj hq0 hq1 hq2 ⊢ <;> omega
      · rcases hfixed with ⟨hqi, hqj⟩
        apply fiveWeight_no_three_transitions_negEight_eight
          (weight k) (weight (R k)) (weight (R (R k)))
            (weight (R (R (R k)))) hkWeight hRkBounds.1 hRkBounds.2
              hRRkBounds.1 hRRkBounds.2 hRRRkBounds.1 hRRRkBounds.2
        all_goals
          rcases hq0 with hq0 | hq0 <;>
            rcases hq1 with hq1 | hq1 <;>
              rcases hq2 with hq2 | hq2 <;>
                dsimp only [qi, qj] at hqi hqj hq0 hq1 hq2 ⊢ <;> omega
      · rcases hfixed with ⟨hqi, hqj⟩
        apply fiveWeight_no_three_transitions_negSix_ten
          (weight k) (weight (R k)) (weight (R (R k)))
            (weight (R (R (R k)))) hkWeight hRkBounds.1 hRkBounds.2
              hRRkBounds.1 hRRkBounds.2 hRRRkBounds.1 hRRRkBounds.2
        all_goals
          rcases hq0 with hq0 | hq0 <;>
            rcases hq1 with hq1 | hq1 <;>
              rcases hq2 with hq2 | hq2 <;>
                dsimp only [qi, qj] at hqi hqj hq0 hq1 hq2 ⊢ <;> omega
    left
    by_cases htwo : R (R p) = p
    · exact Or.inl htwo
    · right
      by_cases hthree : R (R (R p)) = p
      · exact Or.inl hthree
      · right
        by_contra hfour
        exact hnoThree (R p) hp htwo hthree hfour

/-- Lossless fifth-stratum punctured-cycle trichotomy.  A nonconstant
internal transition forces a return after at most four steps.  Otherwise the
only nonconstant-weight survivor is the exact punctured-boundary coefficient
of magnitude `16` or `32`, together with the common available-edge
transition equation from which it was derived. -/
theorem fiveWeightPuncturedPermutation_fifthStratum_shortReturn_or_boundaryCoefficient_or_weight_constant
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta C : G) (H : AddSubgroup G)
    (htransition : ∀ i, i ≠ p → R i ≠ p →
      (weight (R i) - 2 * weight i) • delta + C ∈ H)
    (htwoStep :
      (weight (R p) - 4 * weight (R.symm p)) • delta +
        (3 : ℤ) • C ∈ H)
    (hkernel1632 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • delta ∈ H → e.natAbs = 16 ∨ e.natAbs = 32) :
    (R (R p) = p ∨ R (R (R p)) = p ∨ R (R (R (R p))) = p) ∨
      (((weight (R p) - 4 * weight (R.symm p)) -
          3 * (weight (R i₀) - 2 * weight i₀)).natAbs = 16 ∨
        ((weight (R p) - 4 * weight (R.symm p)) -
          3 * (weight (R i₀) - 2 * weight i₀)).natAbs = 32) ∧
        (∀ i, i ≠ p → R i ≠ p →
          weight (R i) - 2 * weight i =
            weight (R i₀) - 2 * weight i₀) ∨
      ∀ i, i ≠ p → ∀ j, j ≠ p → weight i = weight j := by
  rcases fiveWeightPuncturedPermutation_smallKernelMultipleWithSource_or_weight_constant
      R p i₀ hp hi₀ hRi₀ weight hweight delta C H htransition htwoStep with
    ⟨e, he, helow, hehigh, heMem, hsource⟩ | hconstant
  · have heAbs := hkernel1632 e he helow hehigh heMem
    rcases hsource with ⟨i, hi, hRi, heq⟩ | ⟨heq, hall⟩
    · rcases
          fiveWeightPuncturedPermutation_sixteenOrThirtyTwo_shortReturn_or_transition_constant
            R p hp weight hweight delta C H htransition hkernel1632 with
        hshort | hcoeffConstant
      · exact Or.inl hshort
      · exfalso
        have hs := hcoeffConstant i hi hRi i₀ hi₀ hRi₀
        apply he
        rw [heq]
        exact sub_eq_zero.mpr hs
    · right
      left
      refine ⟨?_, hall⟩
      simpa only [heq] using heAbs
  · exact Or.inr (Or.inr hconstant)

/-- A two-, three-, or four-step return in a full relative-doubling cycle
forces the cyclic-kernel order to divide the corresponding Mersenne number
`3`, `7`, or `15`.  This converts the new fifth-stratum short-return arm into
the same exact odd-order currency used by the global odd-primary descent. -/
theorem addOrderOf_dvd_three_or_seven_or_fifteen_of_isCycle_doubling_shortReturn
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (hcycle : R.IsCycle)
    (hRne : ∀ i, R i ≠ i) (disp : ι → G)
    (hdouble : ∀ i, disp (R i) = 2 • disp i)
    (p : ι) (y : G)
    (hspan : AddSubgroup.closure (Set.range disp) =
      AddSubgroup.zmultiples y)
    (hshort : R (R p) = p ∨ R (R (R p)) = p ∨
      R (R (R (R p))) = p) :
    addOrderOf y ∣ 3 ∨ addOrderOf y ∣ 7 ∨ addOrderOf y ∣ 15 := by
  rcases hshort with htwo | hthree | hfour
  · rcases addOrderOf_dvd_three_or_seven_of_isCycle_doubling_shortReturn
        R hcycle hRne disp hdouble p y hspan (Or.inl htwo) with h3 | h7
    · exact Or.inl h3
    · exact Or.inr (Or.inl h7)
  · rcases addOrderOf_dvd_three_or_seven_of_isCycle_doubling_shortReturn
        R hcycle hRne disp hdouble p y hspan (Or.inr hthree) with h3 | h7
    · exact Or.inl h3
    · exact Or.inr (Or.inl h7)
  · right
    right
    have hspanLe : AddSubgroup.zmultiples y ≤
        AddSubgroup.zmultiples (disp p) := by
      rw [← hspan]
      apply (AddSubgroup.closure_le _).mpr
      rintro v ⟨i, rfl⟩
      obtain ⟨k, hk⟩ := sameCycle_doubling_eq_pow_two_nsmul
        R disp hdouble (hcycle.sameCycle (hRne p) (hRne i))
      rw [hk]
      exact (AddSubgroup.zmultiples (disp p)).nsmul_mem
        (AddSubgroup.mem_zmultiples (disp p)) (2 ^ k)
    have hyMem : y ∈ AddSubgroup.zmultiples (disp p) :=
      hspanLe (AddSubgroup.mem_zmultiples y)
    have hfirst := hdouble p
    have hsecond := hdouble (R p)
    have hthird := hdouble (R (R p))
    have hfourth := hdouble (R (R (R p)))
    rw [hfour, hthird, hsecond, hfirst] at hfourth
    have hpTorsion : 15 • disp p = 0 := by
      calc
        15 • disp p = 2 • (2 • (2 • (2 • disp p))) - disp p := by module
        _ = disp p - disp p := by rw [← hfourth]
        _ = 0 := sub_self _
    have hZle : AddSubgroup.zmultiples (disp p) ≤
        (nsmulAddMonoidHom 15).ker := by
      rw [AddSubgroup.zmultiples_le, AddMonoidHom.mem_ker]
      exact hpTorsion
    have hyTorsion := hZle hyMem
    rw [AddMonoidHom.mem_ker] at hyTorsion
    exact addOrderOf_dvd_of_nsmul_eq_zero hyTorsion

/-- Exact odd-factor classification behind the fifth-stratum short-cycle
arm.  Full odd order, nontriviality, and divisibility by `3`, `7`, or `15`
leave only the four odd factors `3`, `5`, `7`, and `15`. -/
theorem oddFactor_eq_three_or_five_or_seven_or_fifteen_of_fullOrder_smallKernel
    {q r : ℕ} (hq : Odd q) (hrq : r ∣ q) (hrTwo : 2 ≤ r)
    (hfull : q / r = 1)
    (hsmall : r ∣ 3 ∨ r ∣ 7 ∨ r ∣ 15) :
    q = 3 ∨ q = 5 ∨ q = 7 ∨ q = 15 := by
  have hqr : q = r := by
    calc
      q = r * (q / r) := (Nat.mul_div_cancel' hrq).symm
      _ = r := by rw [hfull]; omega
  subst q
  rcases hsmall with h3 | h7 | h15
  · exact Or.inl ((Nat.dvd_prime_two_le (by norm_num) hrTwo).mp h3)
  · exact Or.inr (Or.inr (Or.inl
      ((Nat.dvd_prime_two_le (by norm_num) hrTwo).mp h7)))
  · have hrLe : r ≤ 15 := Nat.le_of_dvd (by omega) h15
    interval_cases r <;> norm_num at h15 <;> omega

/-- Pure endpoint arithmetic for the common-transition boundary arm.  If the
punctured boundary coefficient has magnitude `16` or `32`, the same affine
transition cannot persist for three steps both forward from the successor
and backward into the predecessor.  Only the four boundary weights are
enumerated; the intermediate values are handled symbolically by the affine
recurrences, with only the final predecessor-side value using its uniform
interval bound. -/
theorem fiveWeight_boundaryCoefficient_sixteenOrThirtyTwo_false_of_three_forward_and_backward
    (u v a b x₁ x₂ x₃ z₃ z₂ z₁ : ℤ)
    (hu : u ∈ twoRetainedNormalizedWeightLevels)
    (hv : v ∈ twoRetainedNormalizedWeightLevels)
    (ha : a ∈ twoRetainedNormalizedWeightLevels)
    (hb : b ∈ twoRetainedNormalizedWeightLevels)
    (hz₁ : -4 ≤ z₁) (hz₁' : z₁ ≤ 2)
    (habs : (v - 4 * u - 3 * (b - 2 * a)).natAbs = 16 ∨
      (v - 4 * u - 3 * (b - 2 * a)).natAbs = 32)
    (hforward₁ : x₁ - 2 * v = b - 2 * a)
    (hforward₂ : x₂ - 2 * x₁ = b - 2 * a)
    (hforward₃ : x₃ - 2 * x₂ = b - 2 * a)
    (hbackward₃ : z₂ - 2 * z₃ = b - 2 * a)
    (hbackward₂ : z₁ - 2 * z₂ = b - 2 * a)
    (hbackward₁ : u - 2 * z₁ = b - 2 * a) : False := by
  simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
    Finset.mem_singleton] at hu hv ha hb
  rcases hu with rfl | rfl | rfl | rfl | rfl <;>
    rcases hv with rfl | rfl | rfl | rfl | rfl <;>
      rcases ha with rfl | rfl | rfl | rfl | rfl <;>
        rcases hb with rfl | rfl | rfl | rfl | rfl
  all_goals
    norm_num at habs <;> omega

/-- A common-transition punctured-boundary coefficient of magnitude `16` or
`32` also forces return after at most four steps.  The forward three-edge
segment starts at `R p`; the backward segment ends at `R⁻¹ p`. -/
theorem fiveWeightPuncturedPermutation_boundary_sixteenOrThirtyTwo_shortReturn
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (hboundary :
      ((weight (R p) - 4 * weight (R.symm p)) -
          3 * (weight (R i₀) - 2 * weight i₀)).natAbs = 16 ∨
       ((weight (R p) - 4 * weight (R.symm p)) -
          3 * (weight (R i₀) - 2 * weight i₀)).natAbs = 32)
    (hall : ∀ i, i ≠ p → R i ≠ p →
      weight (R i) - 2 * weight i =
        weight (R i₀) - 2 * weight i₀) :
    R (R p) = p ∨ R (R (R p)) = p ∨ R (R (R (R p))) = p := by
  by_cases htwo : R (R p) = p
  · exact Or.inl htwo
  · right
    by_cases hthree : R (R (R p)) = p
    · exact Or.inl hthree
    · right
      by_contra hfour
      let u : ι := R.symm p
      let z₁ : ι := R.symm u
      let z₂ : ι := R.symm z₁
      let z₃ : ι := R.symm z₂
      have hu : u ≠ p := by
        intro hup
        apply hp
        have happly := R.apply_symm_apply p
        simpa only [u, hup] using happly
      have hz₁ : z₁ ≠ p := by
        intro hz
        have h₁ := congrArg R hz
        have h₂ := congrArg R h₁
        apply htwo
        simpa only [z₁, u, R.apply_symm_apply] using h₂.symm
      have hz₂ : z₂ ≠ p := by
        intro hz
        have h₁ := congrArg R hz
        have h₂ := congrArg R h₁
        have h₃ := congrArg R h₂
        apply hthree
        simpa only [z₂, z₁, u, R.apply_symm_apply] using h₃.symm
      have hz₃ : z₃ ≠ p := by
        intro hz
        have h₁ := congrArg R hz
        have h₂ := congrArg R h₁
        have h₃ := congrArg R h₂
        have h₄ := congrArg R h₃
        apply hfour
        simpa only [z₃, z₂, z₁, u, R.apply_symm_apply] using h₄.symm
      have hRp := twoRetainedNormalizedWeight_bounds (hweight (R p) hp)
      have hz₁Bounds := twoRetainedNormalizedWeight_bounds (hweight z₁ hz₁)
      apply fiveWeight_boundaryCoefficient_sixteenOrThirtyTwo_false_of_three_forward_and_backward
        (weight u) (weight (R p)) (weight i₀) (weight (R i₀))
          (weight (R (R p))) (weight (R (R (R p))))
          (weight (R (R (R (R p))))) (weight z₃) (weight z₂)
          (weight z₁) (hweight u hu) (hweight (R p) hp)
          (hweight i₀ hi₀) (hweight (R i₀) hRi₀)
          hz₁Bounds.1 hz₁Bounds.2
      · simpa only [u] using hboundary
      · exact hall (R p) hp htwo
      · exact hall (R (R p)) htwo hthree
      · exact hall (R (R (R p))) hthree hfour
      · simpa only [z₃, R.apply_symm_apply] using hall z₃ hz₃ (by
          simpa only [z₃, R.apply_symm_apply] using hz₂)
      · simpa only [z₂, R.apply_symm_apply] using hall z₂ hz₂ (by
          simpa only [z₂, R.apply_symm_apply] using hz₁)
      · simpa only [z₁, u, R.apply_symm_apply] using hall z₁ hz₁ (by
          simpa only [z₁, R.apply_symm_apply] using hu)

/-- Final generic fifth-stratum punctured-cycle reduction: every nonconstant
five-weight arm has cycle return at two, three, or four steps.  Hence every
long-cycle survivor already lies in the existing constant-weight/pure-pair
pipeline. -/
theorem fiveWeightPuncturedPermutation_fifthStratum_shortReturn_or_weight_constant
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta C : G) (H : AddSubgroup G)
    (htransition : ∀ i, i ≠ p → R i ≠ p →
      (weight (R i) - 2 * weight i) • delta + C ∈ H)
    (htwoStep :
      (weight (R p) - 4 * weight (R.symm p)) • delta +
        (3 : ℤ) • C ∈ H)
    (hkernel1632 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • delta ∈ H → e.natAbs = 16 ∨ e.natAbs = 32) :
    (R (R p) = p ∨ R (R (R p)) = p ∨ R (R (R (R p))) = p) ∨
      ∀ i, i ≠ p → ∀ j, j ≠ p → weight i = weight j := by
  rcases
      fiveWeightPuncturedPermutation_fifthStratum_shortReturn_or_boundaryCoefficient_or_weight_constant
        R p i₀ hp hi₀ hRi₀ weight hweight delta C H htransition htwoStep
          hkernel1632 with
    hshort | ⟨hboundary, hall⟩ | hconstant
  · exact Or.inl hshort
  · exact Or.inl
      (fiveWeightPuncturedPermutation_boundary_sixteenOrThirtyTwo_shortReturn
        R p i₀ hp hi₀ hRi₀ weight hweight hboundary hall)
  · exact Or.inr hconstant

/-- Provenance-preserving form of the final generic fifth-stratum reduction.
The short-return arm retains the actual nonzero bounded kernel coefficient
that forced it.  This lets odd-primary minimality recover full odd order at
the upstream endpoint rather than losing that information when the cycle is
shortened. -/
theorem fiveWeightPuncturedPermutation_fifthStratum_boundedRelationAndShortReturn_or_weight_constant
    {ι : Type*} [Fintype ι]
    (R : Equiv.Perm ι) (p i₀ : ι) (hp : R p ≠ p)
    (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (weight : ι → ℤ)
    (hweight : ∀ i, i ≠ p →
      weight i ∈ twoRetainedNormalizedWeightLevels)
    (delta C : G) (H : AddSubgroup G)
    (htransition : ∀ i, i ≠ p → R i ≠ p →
      (weight (R i) - 2 * weight i) • delta + C ∈ H)
    (htwoStep :
      (weight (R p) - 4 * weight (R.symm p)) • delta +
        (3 : ℤ) • C ∈ H)
    (hkernel1632 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • delta ∈ H → e.natAbs = 16 ∨ e.natAbs = 32) :
    (∃ e : ℤ, e ≠ 0 ∧ -42 ≤ e ∧ e ≤ 42 ∧ e • delta ∈ H ∧
      (R (R p) = p ∨ R (R (R p)) = p ∨ R (R (R (R p))) = p)) ∨
      ∀ i, i ≠ p → ∀ j, j ≠ p → weight i = weight j := by
  rcases fiveWeightPuncturedPermutation_smallKernelMultipleWithSource_or_weight_constant
      R p i₀ hp hi₀ hRi₀ weight hweight delta C H htransition htwoStep with
    ⟨e, he, helow, hehigh, heMem, hsource⟩ | hconstant
  · rcases
        fiveWeightPuncturedPermutation_fifthStratum_shortReturn_or_weight_constant
          R p i₀ hp hi₀ hRi₀ weight hweight delta C H htransition htwoStep
            hkernel1632 with
      hshort | hconstant
    · exact Or.inl ⟨e, he, helow, hehigh, heMem, hshort⟩
    · exfalso
      rcases hsource with ⟨i, hi, hRi, heq⟩ | ⟨heq, _hall⟩
      · have hsourceEq := hconstant i hi i₀ hi₀
        have htargetEq := hconstant (R i) hRi (R i₀) hRi₀
        apply he
        rw [heq, hsourceEq, htargetEq]
        simp
      · have hsymmNe : R.symm p ≠ p := by
          intro hsymm
          apply hp
          have happly := R.apply_symm_apply p
          simpa only [hsymm] using happly
        have hRpEq := hconstant (R p) hp i₀ hi₀
        have hsymmEq := hconstant (R.symm p) hsymmNe i₀ hi₀
        have hRi₀Eq := hconstant (R i₀) hRi₀ i₀ hi₀
        apply he
        rw [heq, hRpEq, hsymmEq, hRi₀Eq]
        ring
  · exact Or.inr hconstant

/-- Integrated fifth-stratum one-retained endpoint.  In a modulus-minimal
odd-primary survivor, the punctured cycle returns after two, three, or four
steps, or the actual canonical five-weight rows form one of the two
orientation-equivalent pure-pair matrices. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_shortReturn_or_purePair_of_fifthStratum_minimal
    {n q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 5 * q)}
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (a : ZMod (2 ^ 5 * q))
    (p i₀ : Fin d) (hp : R p ≠ p) (hi₀ : i₀ ≠ p)
    (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hretainedMem : g (leaf p) - a ∈ AddSubgroup.zmultiples y) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ((q / addOrderOf y = 1 ∧
          (R (R p) = p ∨ R (R (R p)) = p ∨ R (R (R (R p))) = p)) ∨
        (leaf p = x ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf p = z ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = 0)) := by
  obtain ⟨x, z, weight, cycleWeight, hxB, hzB, hxz, hcomplement,
      hweight, htransition, hcycleValue, hcycleWeight,
      hcycleTransition, hcycleTwoStep⟩ :=
    hrows.oneRetainedCycle_recurrence g y B leaf R a p hp hleafB hdouble
  have hkernel1632 : ∀ e : ℤ, e ≠ 0 → -42 ≤ e → e ≤ 42 →
      e • (g x - g z) ∈ AddSubgroup.zmultiples y →
        e.natAbs = 16 ∨ e.natAbs = 32 := by
    intro e he helow hehigh heMem
    exact
      (hrows.boundedKernelCoefficient_fullOddOrder_and_natAbs_eq_sixteen_or_thirtyTwo_of_fifthStratum_minimal
        hq g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
          e he helow hehigh heMem).2
  have hsplit :=
    fiveWeightPuncturedPermutation_fifthStratum_boundedRelationAndShortReturn_or_weight_constant
      R p i₀ hp hi₀ hRi₀ cycleWeight hcycleWeight
        (g x - g z) ((2 : ℤ) • (g z - a))
          (AddSubgroup.zmultiples y) hcycleTransition hcycleTwoStep hkernel1632
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, ?_⟩
  rcases hsplit with ⟨e, he, helow, hehigh, heMem, hshort⟩ | hconstantCycle
  · have hfull :=
      hrows.boundedKernelCoefficient_fullOddOrder_and_natAbs_eq_sixteen_or_thirtyTwo_of_fifthStratum_minimal
        hq g hg hunique hne y hyq B hminimal x z hxB hzB hxz hcomplement
          e he helow hehigh heMem
    exact Or.inl ⟨hfull.1, hshort⟩
  · have hconstant : ∀ i (hi : leaf i ∈ B) j (hj : leaf j ∈ B),
        weight ⟨leaf i, hi⟩ = weight ⟨leaf j, hj⟩ := by
      intro i hiB j hjB
      have hi : i ≠ p := (hleafB i).1 hiB
      have hj : j ≠ p := (hleafB j).1 hjB
      calc
        weight ⟨leaf i, hiB⟩ = cycleWeight i := (hcycleValue i hiB).symm
        _ = cycleWeight j := hconstantCycle i hi j hj
        _ = weight ⟨leaf j, hjB⟩ := hcycleValue j hjB
    have hiB : leaf i₀ ∈ B := (hleafB i₀).2 hi₀
    have hRiB : leaf (R i₀) ∈ B := (hleafB (R i₀)).2 hRi₀
    let w : ℤ := weight ⟨leaf i₀, hiB⟩
    have hw : w ∈ twoRetainedNormalizedWeightLevels :=
      hweight ⟨leaf i₀, hiB⟩
    have hwEdge : weight ⟨leaf (R i₀), hRiB⟩ = w := by
      simpa only [w] using hconstant (R i₀) hRiB i₀ hiB
    have htransitionSimple :
        (-w) • (g x - g z) + (2 : ℤ) • (g z - a) ∈
          AddSubgroup.zmultiples y := by
      have ht := htransition i₀ hiB hRiB
      rw [hwEdge] at ht
      convert ht using 1
      dsimp only [w]
      module
    have hterminal := constantFiveWeight_transition_terminal
      (g x) (g z) a (AddSubgroup.zmultiples y) w hw htransitionSimple
    have hpNotB : leaf p ∉ B := by
      intro hpB
      exact (hleafB p).1 hpB rfl
    have hpPair : leaf p = x ∨ leaf p = z := by
      have hpComplement : leaf p ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hpNotB⟩
      rw [hcomplement] at hpComplement
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hpComplement
    rcases hpPair with hpX | hpZ
    · have hxMem : g x - a ∈ AddSubgroup.zmultiples y := by
        simpa only [hpX] using hretainedMem
      rcases hterminal.1 hxMem with hsmall | hwMinusTwo
      · rcases hsmall with ⟨e, he, helow, hehigh, heMem⟩
        have heAbs := hkernel1632 e he (by omega) (by omega) heMem
        have habsLe : e.natAbs ≤ 4 := by
          rcases Int.natAbs_eq e with hePos | heNeg
          · have : (e.natAbs : ℤ) ≤ 4 := by omega
            exact_mod_cast this
          · have : (e.natAbs : ℤ) ≤ 4 := by omega
            exact_mod_cast this
        rcases heAbs with h16 | h32 <;> omega
      · exact Or.inr (Or.inl ⟨hpX, by
          intro i hi
          exact (hconstant i hi i₀ hiB).trans hwMinusTwo⟩)
    · have hzMem : g z - a ∈ AddSubgroup.zmultiples y := by
        simpa only [hpZ] using hretainedMem
      rcases hterminal.2 hzMem with hsmall | hwZero
      · rcases hsmall with ⟨e, he, helow, hehigh, heMem⟩
        have heAbs := hkernel1632 e he (by omega) (by omega) heMem
        have habsLe : e.natAbs ≤ 4 := by
          rcases Int.natAbs_eq e with hePos | heNeg
          · have : (e.natAbs : ℤ) ≤ 4 := by omega
            exact_mod_cast this
          · have : (e.natAbs : ℤ) ≤ 4 := by omega
            exact_mod_cast this
        rcases heAbs with h16 | h32 <;> omega
      · exact Or.inr (Or.inr ⟨hpZ, by
          intro i hi
          exact (hconstant i hi i₀ hiB).trans hwZero⟩)

/-- Full-cycle fifth-stratum endpoint in odd-order currency.  Once the leaf
permutation is one cycle and its displacements span `Z*y`, the short-return
arm is exactly `addOrderOf(y) | 3`, `7`, or `15`; every other arm is one of
the two canonical pure-pair orientations. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_smallKernelOrder_or_purePair_of_fifthStratum_minimal
    {n q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 5 * q)}
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (R : Equiv.Perm (Fin d))
    (hcycle : R.IsCycle) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 5 * q))
    (p i₀ : Fin d) (hp : R p ≠ p) (hi₀ : i₀ ≠ p)
    (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (hretainedMem : g (leaf p) - a ∈ AddSubgroup.zmultiples y) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ((q / addOrderOf y = 1 ∧
          (addOrderOf y ∣ 3 ∨ addOrderOf y ∣ 7 ∨ addOrderOf y ∣ 15)) ∨
        (leaf p = x ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = -2) ∨
        (leaf p = z ∧ ∀ i (hi : leaf i ∈ B),
          weight ⟨leaf i, hi⟩ = 0)) := by
  obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, hout⟩ :=
    hrows.oneRetainedCycle_shortReturn_or_purePair_of_fifthStratum_minimal
      hq g hg hunique hne y hyq B hminimal leaf R a p i₀ hp hi₀ hRi₀
        hleafB hdouble hretainedMem
  refine ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, ?_⟩
  rcases hout with ⟨hfullOdd, hshort⟩ | hpureX | hpureZ
  · left
    refine ⟨hfullOdd, ?_⟩
    apply addOrderOf_dvd_three_or_seven_or_fifteen_of_isCycle_doubling_shortReturn
      R hcycle hRne (fun i ↦ g (leaf i) - a) ?_ p y hspan hshort
    intro i
    simpa only [two_nsmul, two_zsmul] using hdouble i
  · exact Or.inr (Or.inl hpureX)
  · exact Or.inr (Or.inr hpureZ)

end MinModulus
