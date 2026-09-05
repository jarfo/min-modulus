/-
# Full primary-exponent routing for dense C2 component primes

HBE routes every prime of the global cyclic order into a row component or the
common pivot component.  This file proves the stronger valuation statement:
the entire primary exponent of that prime survives the avoided scalar and is
carried by one touched Mersenne component.  Consequently the global order is
exactly the lcm of the pivot component and the components reached by the
selected generating rows.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentPrimeCoupling

namespace MinModulus

theorem factorization_addOrderOf_zsmul_eq_of_not_dvd
    {G : Type*} [AddCommGroup G] [Finite G]
    (y : G) (a : ℤ) (p : ℕ)
    (hpScalar : ¬ (p : ℤ) ∣ a) :
    (addOrderOf (a • y)).factorization p =
      (addOrderOf y).factorization p := by
  have hpNatAbs : ¬ p ∣ a.natAbs := by
    intro h
    exact hpScalar (Int.natCast_dvd.mpr h)
  have haNe : a.natAbs ≠ 0 := by
    intro ha
    apply hpNatAbs
    rw [ha]
    exact dvd_zero p
  have horderNe : addOrderOf y ≠ 0 := (addOrderOf_pos y).ne'
  rw [addOrderOf_zsmul_eq_div_gcd,
    Nat.factorization_div (Nat.gcd_dvd_left (addOrderOf y) a.natAbs),
    Nat.factorization_gcd horderNe haNe]
  rw [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.inf_apply,
    Nat.factorization_eq_zero_of_not_dvd hpNatAbs]
  simp

theorem primePower_factorization_dvd_left_or_right_of_dvd_lcm
    {n a b p : ℕ} (hp : p.Prime) (hn : n ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hdvd : n ∣ Nat.lcm a b) :
    p ^ n.factorization p ∣ a ∨ p ^ n.factorization p ∣ b := by
  have hfac : n.factorization p ≤ (Nat.lcm a b).factorization p :=
    ((Nat.factorization_le_iff_dvd hn (Nat.lcm_ne_zero ha hb)).2 hdvd) p
  rw [Nat.factorization_lcm ha hb, Finsupp.sup_apply] at hfac
  rcases (le_max_iff.mp hfac) with hleft | hright
  · exact Or.inl ((hp.pow_dvd_iff_le_factorization ha).2 hleft)
  · exact Or.inr ((hp.pow_dvd_iff_le_factorization hb).2 hright)

theorem primePower_dvd_componentOrder_or_componentOrder_of_exactPair
    {G : Type*} [AddCommGroup G] [Finite G]
    (H K : AddSubgroup G) (y : G) (a : ℤ) {x z : G}
    (hx : x ∈ H) (hz : z ∈ K)
    (htarget : a • y = x - z ∨ a • y = z - x)
    {p : ℕ} (hp : p.Prime) (hpScalar : ¬ (p : ℤ) ∣ a) :
    p ^ (addOrderOf y).factorization p ∣ Nat.card H ∨
      p ^ (addOrderOf y).factorization p ∣ Nat.card K := by
  have htargetDvd : addOrderOf (a • y) ∣
      Nat.lcm (Nat.card H) (Nat.card K) := by
    rcases htarget with hforward | hreverse
    · rw [hforward]
      exact addOrderOf_sub_dvd_lcm_natCard_of_mem H K hx hz
    · rw [hreverse]
      simpa only [Nat.lcm_comm] using
        addOrderOf_sub_dvd_lcm_natCard_of_mem K H hz hx
  have hHne : Nat.card H ≠ 0 := (Nat.card_pos).ne'
  have hKne : Nat.card K ≠ 0 := (Nat.card_pos).ne'
  have hroute := primePower_factorization_dvd_left_or_right_of_dvd_lcm
    hp (addOrderOf_pos (a • y)).ne' hHne hKne htargetDvd
  rw [factorization_addOrderOf_zsmul_eq_of_not_dvd
    y a p hpScalar] at hroute
  exact hroute

open Finset

/-- Full primary-exponent refinement of HBE's prime coverage.  For every
prime of the global order, one scalar avoids that prime and one of the two
touched component Mersenne numbers contains the entire corresponding
prime-power part of the global order. -/
def GeneratingPivotComponentMersennePrimaryCoverage
    {G : Type*} [AddCommGroup G] {d : ℕ}
    (y : G) (R P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (scalar : ↥J → ℤ) (pivot : Fin d) : Prop :=
  ∀ p : ℕ, p.Prime → p ∣ addOrderOf y →
    ∃ j : ↥J, ¬ (p : ℤ) ∣ scalar j ∧
      (p ^ (addOrderOf y).factorization p ∣
          2 ^ (R.cycleOf (j : Fin d)).support.card - 1 ∨
        p ^ (addOrderOf y).factorization p ∣
          2 ^ (R.cycleOf (P pivot)).support.card - 1)

/-- The lcm of the pivot component and all relative components reached by the
selected generating rows. -/
def pivotRowComponentMersenneLcm
    {d : ℕ} (R P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (pivot : Fin d) : ℕ :=
  Nat.lcm (2 ^ (R.cycleOf (P pivot)).support.card - 1)
    (Finset.univ.lcm (fun j : ↥J ↦
      2 ^ (R.cycleOf (j : Fin d)).support.card - 1))

/-- Full primary-exponent coverage is exactly what is needed to show that the
global cyclic order divides the selected pivot/row component lcm. -/
theorem addOrderOf_dvd_pivotRowComponentMersenneLcm_of_primaryCoverage
    {G : Type*} [AddCommGroup G] [Finite G] {d : ℕ}
    (y : G) (R P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (scalar : ↥J → ℤ) (pivot : Fin d)
    (hcoverage : GeneratingPivotComponentMersennePrimaryCoverage
      y R P J scalar pivot) :
    addOrderOf y ∣ pivotRowComponentMersenneLcm R P J pivot := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p k hp hpk
  by_cases hk : k = 0
  · subst k
    simp
  have hpOrder : p ∣ addOrderOf y := by
    have hpPk : p ∣ p ^ k := by
      rw [show k = (k - 1) + 1 by omega, pow_succ]
      exact dvd_mul_left p (p ^ (k - 1))
    exact hpPk.trans hpk
  obtain ⟨j, _hpScalar, hroute⟩ :=
    hcoverage p hp hpOrder
  have hkFactor : k ≤ (addOrderOf y).factorization p :=
    (hp.pow_dvd_iff_le_factorization (addOrderOf_pos y).ne').1 hpk
  have hkMax : p ^ k ∣ p ^ (addOrderOf y).factorization p :=
    pow_dvd_pow p hkFactor
  rcases hroute with hrow | hpivot
  · exact (hkMax.trans hrow).trans
      ((Finset.dvd_lcm (s := Finset.univ)
          (f := fun i : ↥J ↦
            2 ^ (R.cycleOf (i : Fin d)).support.card - 1)
          (Finset.mem_univ j)).trans (Nat.dvd_lcm_right _ _))
  · exact (hkMax.trans hpivot).trans (Nat.dvd_lcm_left _ _)

variable {n N d : ℕ}

/-- The exact-pair coupling preserves not just the presence of a global
prime but its full exponent in the global cyclic order. -/
theorem generatingPivotStar_primePower_componentMersenne_coverage
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf center : Fin d → Fin n) (P R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (J : Finset (Fin d)) (scalar : ↥J → ℤ)
    (coeff : ↥J → Fin n → ℤ) (pivot : Fin d)
    (hpairs : ∀ j : ↥J,
      ExactSignedPairWitness g (scalar j • y) (coeff j)
        (center (P.symm (j : Fin d))) (center pivot))
    (harithmetic : GeneratingScalarArithmetic y scalar)
    (hprofile : RelativeDoublingProperComponentMersenneLcmProfile
      g y base leaf R) :
    GeneratingPivotComponentMersennePrimaryCoverage
      y R P J scalar pivot := by
  classical
  let disp : Fin d → ZMod N := fun i ↦ g (leaf i) - base
  intro p hp hpOrder
  obtain ⟨j, hpScalar⟩ := harithmetic.choose_spec.2 p hp hpOrder
  let Cj : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (j : Fin d)
  let Cp : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (P pivot)
  have hjSupport : (j : Fin d) ∈ (Cj : Equiv.Perm (Fin d)).support :=
    mem_support_permutationCycleFactorOf R hRne (j : Fin d)
  have hpSupport : P pivot ∈ (Cp : Equiv.Perm (Fin d)).support :=
    mem_support_permutationCycleFactorOf R hRne (P pivot)
  have hjMem : disp (j : Fin d) ∈
      permutationCycleFactorSpan R disp Cj :=
    AddSubgroup.subset_closure ⟨⟨(j : Fin d), hjSupport⟩, rfl⟩
  have hpMem : disp (P pivot) ∈
      permutationCycleFactorSpan R disp Cp :=
    AddSubgroup.subset_closure ⟨⟨P pivot, hpSupport⟩, rfl⟩
  have htarget : scalar j • y =
        disp (j : Fin d) - disp (P pivot) ∨
      scalar j • y = disp (P pivot) - disp (j : Fin d) := by
    rcases (hpairs j).2.1 with hforward | hreverse
    · left
      calc
        scalar j • y =
            g (center (P.symm (j : Fin d))) - g (center pivot) :=
          hforward.2.2
        _ = g (leaf (j : Fin d)) - g (leaf (P pivot)) := by
          rw [hcenter (P.symm (j : Fin d)), P.apply_symm_apply,
            hcenter pivot]
        _ = disp (j : Fin d) - disp (P pivot) := by
          simp only [disp]
          abel
    · right
      calc
        scalar j • y =
            g (center pivot) - g (center (P.symm (j : Fin d))) :=
          hreverse.2.2
        _ = g (leaf (P pivot)) - g (leaf (j : Fin d)) := by
          rw [hcenter pivot, hcenter (P.symm (j : Fin d)),
            P.apply_symm_apply]
        _ = disp (P pivot) - disp (j : Fin d) := by
          simp only [disp]
          abel
  have hpComponent :=
    primePower_dvd_componentOrder_or_componentOrder_of_exactPair
      (permutationCycleFactorSpan R disp Cj)
      (permutationCycleFactorSpan R disp Cp)
      y (scalar j) hjMem hpMem htarget hp hpScalar
  rw [hprofile.2.1 Cj, hprofile.2.1 Cp] at hpComponent
  refine ⟨j, hpScalar, ?_⟩
  simpa only [Cj, Cp, permutationCycleFactorOf] using hpComponent

/-- In the HBD profile, primary coverage identifies the global order exactly
with the lcm of the pivot component and the components reached by the selected
generating rows. -/
theorem addOrderOf_eq_pivotRowComponentMersenneLcm_of_primaryCoverage
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (P R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (J : Finset (Fin d))
    (scalar : ↥J → ℤ) (pivot : Fin d)
    (hcoverage : GeneratingPivotComponentMersennePrimaryCoverage
      y R P J scalar pivot)
    (hprofile : RelativeDoublingProperComponentMersenneLcmProfile
      g y base leaf R) :
    addOrderOf y = pivotRowComponentMersenneLcm R P J pivot := by
  apply Nat.dvd_antisymm
  · exact addOrderOf_dvd_pivotRowComponentMersenneLcm_of_primaryCoverage
      y R P J scalar pivot hcoverage
  · apply Nat.lcm_dvd
    · let Cp : ↥R.cycleFactorsFinset :=
        permutationCycleFactorOf R hRne (P pivot)
      have hdiv := (hprofile.1.2.2 Cp).2.2.1
      rw [hprofile.2.1 Cp] at hdiv
      simpa only [Cp, permutationCycleFactorOf] using hdiv
    · apply Finset.lcm_dvd
      intro j hj
      let Cj : ↥R.cycleFactorsFinset :=
        permutationCycleFactorOf R hRne (j : Fin d)
      have hdiv := (hprofile.1.2.2 Cj).2.2.1
      rw [hprofile.2.1 Cj] at hdiv
      simpa only [Cj, permutationCycleFactorOf] using hdiv

/-- HBE's retained-external/pivot carrier with full primary-exponent routing
attached to its internal exact-pair arm. -/
def CycleCenterSparseRetainedExternalOrComponentMersennePrimaryPivotStar
    (g : Fin n → ZMod N) (y : ZMod N) (B : Finset (Fin n))
    {d : ℕ} (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d)) : Prop :=
  ∃ scalar : ↥J → ℤ, ∃ coeff : ↥J → Fin n → ℤ,
    d - 1 ≤ J.card ∧ Function.Injective coeff ∧
    (∀ j, scalar j • y ≠ 0 ∧
      Witness g (scalar j • y) (coeff j)) ∧
    (∀ (j : ↥J) x, x ∈ B →
      x ≠ center (P.symm (j : Fin d)) → coeff j x = 0) ∧
    ((∃ j : ↥J,
        HasRetainedExternalCenterSupport center B (coeff j)) ∨
      ∃ pivot : Fin d, center pivot ∉ B ∧
        (∀ j : ↥J,
          ExactSignedPairWitness g (scalar j • y) (coeff j)
            (center (P.symm j)) (center pivot)) ∧
        AddSubgroup.closure
          (Set.range (fun j : ↥J ↦ scalar j • y)) =
            AddSubgroup.zmultiples y ∧
        GeneratingScalarArithmetic y scalar ∧
        GeneratingPivotComponentMersennePrimeCoverage
          y R P J scalar pivot ∧
        GeneratingPivotComponentMersennePrimaryCoverage
          y R P J scalar pivot)

/-- Upgrade HBE's coupled pivot carrier from prime presence to the full
primary exponent, preserving every row and every alternative. -/
theorem cycleCenterSparse_retainedExternal_or_componentMersennePrimaryPivotStar
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N) (B : Finset (Fin n))
    {d : ℕ} (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hstar : CycleCenterSparseRetainedExternalOrComponentMersennePrimePivotStar
      g y B center P J R)
    (hprofile : RelativeDoublingProperComponentMersenneLcmProfile
      g y base leaf R) :
    CycleCenterSparseRetainedExternalOrComponentMersennePrimaryPivotStar
      g y B center P J R := by
  rcases hstar with
    ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      hexternal |
        ⟨pivot, hpivot, hpairs, hgenerate, harithmetic, hprime⟩⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inl hexternal⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inr ⟨pivot, hpivot, hpairs, hgenerate, harithmetic, hprime,
        generatingPivotStar_primePower_componentMersenne_coverage
          g y base leaf center P R hRne hcenter J scalar coeff pivot
            hpairs harithmetic hprofile⟩⟩

/-- The live HBE state with the full primary exponent of each global prime
routed into a touched row or pivot Mersenne component. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimaryCoverageStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d)) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveProperComponentMersenneLcmStateFamily
      g y base B leaf J R ∧
    CycleCenterSparseRetainedExternalOrComponentMersennePrimaryPivotStar
      g y B center P J R

/-- HBE's public state already contains all data needed for the stronger
primary-exponent coupling; no new global endpoint wrapper is required. -/
theorem TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimeCoverageStateFamily.componentMersennePrimaryCoverage
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hfamily :
      TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimeCoverageStateFamily
        g y base B leaf center P J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentMersennePrimaryCoverageStateFamily
        g y base B leaf center P J R := by
  exact ⟨hfamily.1,
    cycleCenterSparse_retainedExternal_or_componentMersennePrimaryPivotStar
      g y base B leaf center P J R hRne hcenter hfamily.2 hfamily.1.2⟩

end MinModulus
