/-
# Scalar absorption outside the row and pivot components

HBH identifies the global cyclic-kernel order with a product of pairwise
coprime component Mersenne orders.  An exact row-to-pivot difference has
order bounded by the lcm of those two touched component orders.  Therefore
every untouched component factor must be absorbed by the row's integer
scalar.  Pairwise coprimality promotes the individual divisibilities to
divisibility by the complete untouched-component product.

The final state-family refinement attaches this simultaneous rowwise law to
the live component-spanning C2 carrier while preserving its retained-external
exit.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentProductSaturation

namespace MinModulus

/-- If a factor of the order of `y` is coprime to an upper bound for the
order of `a • y`, then that factor must divide the integer scalar `a`. -/
theorem natCast_dvd_scalar_of_factor_coprime_targetOrderBound
    {G : Type*} [AddCommGroup G] [Finite G]
    (y : G) (a : ℤ) {f k : ℕ}
    (hfOrder : f ∣ addOrderOf y) (hcoprime : Nat.Coprime f k)
    (htarget : addOrderOf (a • y) ∣ k) : (f : ℤ) ∣ a := by
  have hquotientDvd : addOrderOf y / (addOrderOf y).gcd a.natAbs ∣ k := by
    rwa [← addOrderOf_zsmul_eq_div_gcd y a]
  have hcoprimeQuotient : Nat.Coprime f
      (addOrderOf y / (addOrderOf y).gcd a.natAbs) :=
    hcoprime.of_dvd_right hquotientDvd
  have hfactor : (addOrderOf y).gcd a.natAbs *
      (addOrderOf y / (addOrderOf y).gcd a.natAbs) = addOrderOf y :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
  have hfProduct : f ∣ (addOrderOf y).gcd a.natAbs *
      (addOrderOf y / (addOrderOf y).gcd a.natAbs) := by
    rw [hfactor]
    exact hfOrder
  have hfGcd : f ∣ (addOrderOf y).gcd a.natAbs :=
    hcoprimeQuotient.dvd_of_dvd_mul_right hfProduct
  exact Int.natCast_dvd.mpr
    (hfGcd.trans (Nat.gcd_dvd_right _ _))

open Finset

variable {n N d : ℕ}

/-- In the HBH coprime component product, an exact row-to-pivot difference
forces the row scalar to absorb every third component's full Mersenne order.
-/
theorem componentMersenne_dvd_scalar_of_exactPair_of_ne
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf center : Fin d → Fin n) (P R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    {J : Finset (Fin d)} (j : ↥J) (scalar : ↥J → ℤ)
    (coeff : ↥J → Fin n → ℤ) (pivot : Fin d)
    (hpair : ExactSignedPairWitness g (scalar j • y) (coeff j)
      (center (P.symm (j : Fin d))) (center pivot))
    (hprofile : RelativeDoublingProperComponentProductProfile
      g y base leaf R)
    (C : ↥R.cycleFactorsFinset)
    (hCrow : C ≠ permutationCycleFactorOf R hRne (j : Fin d))
    (hCpivot : C ≠ permutationCycleFactorOf R hRne (P pivot)) :
    ((2 ^ (C : Equiv.Perm (Fin d)).support.card - 1 : ℕ) : ℤ) ∣
      scalar j := by
  classical
  let disp : Fin d → ZMod N := fun i ↦ g (leaf i) - base
  let Cj : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (j : Fin d)
  let Cp : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (P pivot)
  let MC : ℕ := 2 ^ (C : Equiv.Perm (Fin d)).support.card - 1
  let Mj : ℕ := 2 ^ (Cj : Equiv.Perm (Fin d)).support.card - 1
  let Mp : ℕ := 2 ^ (Cp : Equiv.Perm (Fin d)).support.card - 1
  have hjSupport : (j : Fin d) ∈
      (Cj : Equiv.Perm (Fin d)).support :=
    mem_support_permutationCycleFactorOf R hRne (j : Fin d)
  have hpSupport : P pivot ∈
      (Cp : Equiv.Perm (Fin d)).support :=
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
    rcases hpair.2.1 with hforward | hreverse
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
  have htargetDvd : addOrderOf (scalar j • y) ∣ Nat.lcm Mj Mp := by
    rcases htarget with hforward | hreverse
    · rw [hforward]
      have hdiv := addOrderOf_sub_dvd_lcm_natCard_of_mem
        (permutationCycleFactorSpan R disp Cj)
        (permutationCycleFactorSpan R disp Cp) hjMem hpMem
      rw [hprofile.1.2.1 Cj, hprofile.1.2.1 Cp] at hdiv
      simpa only [Mj, Mp] using hdiv
    · rw [hreverse]
      have hdiv := addOrderOf_sub_dvd_lcm_natCard_of_mem
        (permutationCycleFactorSpan R disp Cp)
        (permutationCycleFactorSpan R disp Cj) hpMem hjMem
      rw [hprofile.1.2.1 Cp, hprofile.1.2.1 Cj,
        Nat.lcm_comm] at hdiv
      exact hdiv
  have hfactorOrder : MC ∣ addOrderOf y := by
    have hdiv := (hprofile.1.1.2.2 C).2.2.1
    rw [hprofile.1.2.1 C] at hdiv
    exact hdiv
  have hcoprimeRow : Nat.Coprime MC Mj := by
    exact hprofile.2.2.1 C Cj (by simpa only [Cj] using hCrow)
  have hcoprimePivot : Nat.Coprime MC Mp := by
    exact hprofile.2.2.1 C Cp (by simpa only [Cp] using hCpivot)
  have hcoprimeLcm : Nat.Coprime MC (Nat.lcm Mj Mp) :=
    (hcoprimeRow.mul_right hcoprimePivot).of_dvd_right
      (Nat.lcm_dvd_mul Mj Mp)
  simpa only [MC] using
    (natCast_dvd_scalar_of_factor_coprime_targetOrderBound
      y (scalar j) hfactorOrder hcoprimeLcm htargetDvd)

/-- The product of all components other than the row and pivot components
divides the exact-pair scalar.  Pairwise coprimality is essential here: it
upgrades the componentwise divisibilities to one product divisibility. -/
theorem componentComplementMersenneProduct_dvd_scalar_of_exactPair
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf center : Fin d → Fin n) (P R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    {J : Finset (Fin d)} (j : ↥J) (scalar : ↥J → ℤ)
    (coeff : ↥J → Fin n → ℤ) (pivot : Fin d)
    (hpair : ExactSignedPairWitness g (scalar j • y) (coeff j)
      (center (P.symm (j : Fin d))) (center pivot))
    (hprofile : RelativeDoublingProperComponentProductProfile
      g y base leaf R) :
    (∏ C ∈ (Finset.univ.filter fun C : ↥R.cycleFactorsFinset ↦
          C ≠ permutationCycleFactorOf R hRne (j : Fin d) ∧
          C ≠ permutationCycleFactorOf R hRne (P pivot)),
        ((2 ^ (C : Equiv.Perm (Fin d)).support.card - 1 : ℕ) : ℤ)) ∣
      scalar j := by
  classical
  let Cj : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (j : Fin d)
  let Cp : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (P pivot)
  let K : Finset ↥R.cycleFactorsFinset :=
    Finset.univ.filter fun C ↦ C ≠ Cj ∧ C ≠ Cp
  have hpairwise : (K : Set ↥R.cycleFactorsFinset).Pairwise
      (fun C D ↦ IsCoprime
        ((2 ^ (C : Equiv.Perm (Fin d)).support.card - 1 : ℕ) : ℤ)
        ((2 ^ (D : Equiv.Perm (Fin d)).support.card - 1 : ℕ) : ℤ)) := by
    intro C hC D hD hne
    exact Nat.Coprime.isCoprime
      (hprofile.2.2.1 C D hne)
  have hdivEach : ∀ C ∈ K,
      ((2 ^ (C : Equiv.Perm (Fin d)).support.card - 1 : ℕ) : ℤ) ∣
        scalar j := by
    intro C hC
    have hne := (Finset.mem_filter.mp hC).2
    apply componentMersenne_dvd_scalar_of_exactPair_of_ne
      g y base leaf center P R hRne hcenter j scalar coeff pivot
        hpair hprofile C
    · simpa only [Cj] using hne.1
    · simpa only [Cp] using hne.2
  have hprodDvd := Finset.prod_dvd_of_coprime hpairwise hdivEach
  simpa only [K, Cj, Cp] using hprodDvd

/-- Rowwise scalar absorption forced by a component-spanning exact-pair
star in the pairwise-coprime component product. -/
def GeneratingPivotComponentComplementProductDivisibility
    {d : ℕ}
    (R P : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (J : Finset (Fin d)) (scalar : ↥J → ℤ) (pivot : Fin d) : Prop :=
  ∀ j : ↥J,
    (∏ C ∈ (Finset.univ.filter fun C : ↥R.cycleFactorsFinset ↦
        C ≠ permutationCycleFactorOf R hRne (j : Fin d) ∧
        C ≠ permutationCycleFactorOf R hRne (P pivot)),
      ((2 ^ (C : Equiv.Perm (Fin d)).support.card - 1 : ℕ) : ℤ)) ∣
        scalar j

/-- Promote all rows of the component-spanning star to simultaneous
complement-product scalar divisibility. -/
theorem generatingPivotStar_componentComplementProductDivisibility
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf center : Fin d → Fin n) (P R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (J : Finset (Fin d)) (scalar : ↥J → ℤ)
    (coeff : ↥J → Fin n → ℤ) (pivot : Fin d)
    (hpairs : ∀ j : ↥J,
      ExactSignedPairWitness g (scalar j • y) (coeff j)
        (center (P.symm (j : Fin d))) (center pivot))
    (hprofile : RelativeDoublingProperComponentProductProfile
      g y base leaf R) :
    GeneratingPivotComponentComplementProductDivisibility
      R P hRne J scalar pivot := by
  intro j
  exact componentComplementMersenneProduct_dvd_scalar_of_exactPair
    g y base leaf center P R hRne hcenter j scalar coeff pivot
      (hpairs j) hprofile

/-- HBG's retained-external/pivot carrier after every internal row scalar is
known to absorb the product of all untouched component orders. -/
def CycleCenterSparseRetainedExternalOrComponentAbsorbingPivotStar
    (g : Fin n → ZMod N) (y : ZMod N) (B : Finset (Fin n))
    (center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) : Prop :=
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
          y R P J scalar pivot ∧
        GeneratingPivotComponentSpanningStar
          g y center P R J scalar coeff pivot ∧
        addOrderOf y = rowComponentMersenneLcm R J ∧
        GeneratingPivotComponentComplementProductDivisibility
          R P hRne J scalar pivot)

/-- Upgrade HBG's component-spanning pivot star with HBH's exact
complement-product absorption law. -/
theorem cycleCenterSparse_retainedExternal_or_componentAbsorbingPivotStar
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hstar : CycleCenterSparseRetainedExternalOrComponentSpanningPivotStar
      g y B center P J R)
    (hprofile : RelativeDoublingProperComponentProductProfile
      g y base leaf R) :
    CycleCenterSparseRetainedExternalOrComponentAbsorbingPivotStar
      g y B center P J R hRne := by
  rcases hstar with
    ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      hexternal |
        ⟨pivot, hpivot, hpairs, hgenerate, harithmetic, hprime,
          hprimary, hspanning, horder⟩⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inl hexternal⟩
  · exact ⟨scalar, coeff, hJcard, hcoeffInj, hrows, hprivate,
      Or.inr ⟨pivot, hpivot, hpairs, hgenerate, harithmetic, hprime,
        hprimary, hspanning, horder,
        generatingPivotStar_componentComplementProductDivisibility
          g y base leaf center P R hRne hcenter J scalar coeff pivot
            hpairs hprofile⟩⟩

/-- The live HBH state after the component-spanning exact rows have been
coupled to their full untouched-component products. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentAbsorptionStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveComponentProductStateFamily
      g y base B leaf center P J R ∧
    CycleCenterSparseRetainedExternalOrComponentAbsorbingPivotStar
      g y B center P J R hRne

/-- The public HBH state already contains everything needed for the
component-complement scalar absorption refinement. -/
theorem TwoRetainedPivotAlignedDensePrimitiveComponentProductStateFamily.componentAbsorption
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (hcenter : ∀ i, center i = leaf (P i))
    (hfamily :
      TwoRetainedPivotAlignedDensePrimitiveComponentProductStateFamily
        g y base B leaf center P J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentAbsorptionStateFamily
        g y base B leaf center P J R hRne := by
  exact ⟨hfamily,
    cycleCenterSparse_retainedExternal_or_componentAbsorbingPivotStar
      g y base B leaf center P J R hRne hcenter hfamily.1.2 hfamily.2⟩

end MinModulus
