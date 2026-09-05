/-
# Exact CRT scalar gcds for the dense C2 component star

The sharp cross-component target orders from HBK and the global saturated
component product determine the gcd of every selected scalar with the cyclic
kernel order.  It is exactly the product of the untouched component factors.
This module installs that CRT classification in the live C2 endpoint.
-/
import MinModulus.G1OddPrimaryFullCycleC2DensePrimitiveComponentExactOrder

namespace MinModulus

open Finset

/-- Split two distinct named factors from a finite product. -/
theorem prod_eq_filter_ne_two_mul
    {ι M : Type*} [DecidableEq ι] [CommMonoid M]
    (s : Finset ι) (f : ι → M) {a b : ι}
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    ∏ i ∈ s, f i =
      (∏ i ∈ s.filter (fun i ↦ i ≠ a ∧ i ≠ b), f i) * f a * f b := by
  have hbErase : b ∈ s.erase a := Finset.mem_erase.mpr ⟨hab.symm, hb⟩
  have hfilter : s.filter (fun i ↦ i ≠ a ∧ i ≠ b) =
      (s.erase a).erase b := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_erase]
    aesop
  calc
    ∏ i ∈ s, f i = (∏ i ∈ s.erase a, f i) * f a :=
      (Finset.prod_erase_mul s f ha).symm
    _ = ((∏ i ∈ (s.erase a).erase b, f i) * f b) * f a := by
      rw [Finset.prod_erase_mul (s.erase a) f hbErase]
    _ = (∏ i ∈ s.filter (fun i ↦ i ≠ a ∧ i ≠ b), f i) *
        f a * f b := by
      rw [hfilter]
      ac_rfl

variable {G : Type*} [AddCommGroup G] [Finite G]

/-- If the ambient order is a product of positive pairwise-coprime factors
and `a • y` has exactly two named factors as its order, then the gcd of the
ambient order with `|a|` is exactly the product of all untouched factors. -/
theorem gcd_addOrderOf_natAbs_eq_complementProduct_of_targetOrder_eq_twoFactors
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (y : G) (a : ℤ) (f : ι → ℕ) (u v : ι) (huv : u ≠ v)
    (hpositive : ∀ i, 0 < f i)
    (horder : addOrderOf y = ∏ i, f i)
    (htarget : addOrderOf (a • y) = f u * f v) :
    (addOrderOf y).gcd a.natAbs =
      ∏ i ∈ (Finset.univ.filter fun i : ι ↦ i ≠ u ∧ i ≠ v), f i := by
  let Q : ℕ :=
    ∏ i ∈ (Finset.univ.filter fun i : ι ↦ i ≠ u ∧ i ≠ v), f i
  let D : ℕ := (addOrderOf y).gcd a.natAbs
  let K : ℕ := f u * f v
  have hprod : addOrderOf y = Q * K := by
    rw [horder]
    have hsplit := prod_eq_filter_ne_two_mul
      (Finset.univ : Finset ι) f (Finset.mem_univ u)
        (Finset.mem_univ v) huv
    simpa only [Q, K, Nat.mul_assoc] using hsplit
  have hquotient : addOrderOf y / D = K := by
    rw [addOrderOf_zsmul_eq_div_gcd] at htarget
    simpa only [D, K] using htarget
  have hDpos : 0 < D :=
    Nat.gcd_pos_of_pos_left a.natAbs (addOrderOf_pos y)
  have hDdvd : D ∣ addOrderOf y := Nat.gcd_dvd_left _ _
  have horderMul : addOrderOf y = K * D :=
    (Nat.div_eq_iff_eq_mul_left hDpos hDdvd).mp hquotient
  have hKpos : 0 < K := mul_pos (hpositive u) (hpositive v)
  have hcancel : K * D = K * Q := by
    calc
      K * D = addOrderOf y := horderMul.symm
      _ = Q * K := hprod
      _ = K * Q := Nat.mul_comm _ _
  simpa only [D, Q] using Nat.eq_of_mul_eq_mul_left hKpos hcancel

variable {n N d : ℕ}

/-- HBK's sharp cross-component target order identifies the scalar gcd with
the complete untouched-component product. -/
theorem componentComplementMersenneProduct_eq_gcd_of_exactTargetOrder
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R P : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) {J : Finset (Fin d)}
    (j : ↥J) (scalar : ↥J → ℤ) (pivot : Fin d)
    (hprofile : RelativeDoublingProperComponentProductProfile
      g y base leaf R)
    (hne : permutationCycleFactorOf R hRne (j : Fin d) ≠
      permutationCycleFactorOf R hRne (P pivot))
    (htarget : addOrderOf (scalar j • y) =
      (2 ^ (R.cycleOf (j : Fin d)).support.card - 1) *
        (2 ^ (R.cycleOf (P pivot)).support.card - 1)) :
    (addOrderOf y).gcd (scalar j).natAbs =
      ∏ C ∈ (Finset.univ.filter fun C : ↥R.cycleFactorsFinset ↦
          C ≠ permutationCycleFactorOf R hRne (j : Fin d) ∧
          C ≠ permutationCycleFactorOf R hRne (P pivot)),
        (2 ^ (C : Equiv.Perm (Fin d)).support.card - 1) := by
  classical
  let Cj : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (j : Fin d)
  let Cp : ↥R.cycleFactorsFinset :=
    permutationCycleFactorOf R hRne (P pivot)
  let f : ↥R.cycleFactorsFinset → ℕ := fun C ↦
    2 ^ (C : Equiv.Perm (Fin d)).support.card - 1
  have hpositive : ∀ C : ↥R.cycleFactorsFinset, 0 < f C := by
    intro C
    have hcycle : (C : Equiv.Perm (Fin d)).IsCycle :=
      (Equiv.Perm.mem_cycleFactorsFinset_iff.mp C.property).1
    have htwo := hcycle.two_le_card_support
    have hpow : 1 < 2 ^ (C : Equiv.Perm (Fin d)).support.card :=
      one_lt_pow₀ (by omega) (Nat.ne_of_gt (by omega))
    dsimp only [f]
    omega
  have htarget' : addOrderOf (scalar j • y) = f Cj * f Cp := by
    simpa only [f, Cj, Cp, permutationCycleFactorOf] using htarget
  have hgcd :=
    gcd_addOrderOf_natAbs_eq_complementProduct_of_targetOrder_eq_twoFactors
      y (scalar j) f Cj Cp (by simpa only [Cj, Cp] using hne)
        hpositive hprofile.2.1 htarget'
  simpa only [f, Cj, Cp] using hgcd

/-- Exact CRT gcd classification for every selected row outside the pivot
component. -/
def GeneratingPivotComponentComplementProductGcdExactness
    {G : Type*} [AddCommGroup G] {d : ℕ}
    (y : G) (R P : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (J : Finset (Fin d)) (scalar : ↥J → ℤ) (pivot : Fin d) : Prop :=
  ∀ j : ↥J,
    permutationCycleFactorOf R hRne (j : Fin d) ≠
        permutationCycleFactorOf R hRne (P pivot) →
      (addOrderOf y).gcd (scalar j).natAbs =
        ∏ C ∈ (Finset.univ.filter fun C : ↥R.cycleFactorsFinset ↦
            C ≠ permutationCycleFactorOf R hRne (j : Fin d) ∧
            C ≠ permutationCycleFactorOf R hRne (P pivot)),
          (2 ^ (C : Equiv.Perm (Fin d)).support.card - 1)

/-- HBK's simultaneous exact target orders give simultaneous exact scalar
gcds with the global component product. -/
theorem GeneratingPivotComponentPairOrderExactness.componentComplementProductGcdExactness
    [NeZero N]
    (g : Fin n → ZMod N) (y base : ZMod N)
    (leaf : Fin d → Fin n) (R P : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) (J : Finset (Fin d))
    (scalar : ↥J → ℤ) (pivot : Fin d)
    (hexact : GeneratingPivotComponentPairOrderExactness
      y R P hRne J scalar pivot)
    (hprofile : RelativeDoublingProperComponentProductProfile
      g y base leaf R) :
    GeneratingPivotComponentComplementProductGcdExactness
      y R P hRne J scalar pivot := by
  intro j hne
  exact componentComplementMersenneProduct_eq_gcd_of_exactTargetOrder
    g y base leaf R P hRne j scalar pivot hprofile hne (hexact j hne)

/-- The live exact-order state equipped with its uniform CRT projection:
any selected exact-order star on its product profile has scalar gcd equal to
the complete untouched-component product. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentCRTStateFamily
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i) : Prop :=
  TwoRetainedPivotAlignedDensePrimitiveComponentExactOrderStateFamily
      g y base B leaf center P J R hRne ∧
    ∀ (scalar : ↥J → ℤ) (pivot : Fin d),
      GeneratingPivotComponentPairOrderExactness
          y R P hRne J scalar pivot →
        GeneratingPivotComponentComplementProductGcdExactness
          y R P hRne J scalar pivot

/-- Attach the exact CRT gcd projection to HBK's live state. -/
theorem TwoRetainedPivotAlignedDensePrimitiveComponentExactOrderStateFamily.componentCRT
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q))
    (y base : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (leaf center : Fin d → Fin n) (P : Equiv.Perm (Fin d))
    (J : Finset (Fin d)) (R : Equiv.Perm (Fin d))
    (hRne : ∀ i, R i ≠ i)
    (hfamily :
      TwoRetainedPivotAlignedDensePrimitiveComponentExactOrderStateFamily
        g y base B leaf center P J R hRne) :
    TwoRetainedPivotAlignedDensePrimitiveComponentCRTStateFamily
        g y base B leaf center P J R hRne := by
  refine ⟨hfamily, ?_⟩
  intro scalar pivot hexact
  exact hexact.componentComplementProductGcdExactness
    g y base leaf R P hRne J scalar pivot hfamily.1.2

variable {m : ℕ}

/-- HBK's terminal with the exact scalar-gcd CRT classification attached to
its component state. -/
def TwoRetainedPivotAlignedDensePrimitiveComponentCRTTerminal
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf center : Fin d → Fin (m + 1))
    (P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d)) : Prop :=
  q / addOrderOf y ≠ 1 ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      ∃ B₀ : Finset (Fin (m + 1)),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ m + 1 - B₀.card) ∨
    (q / addOrderOf y = 1 ∧ d + 5 ≤ m + 1 ∧
      TwoRetainedPivotAlignedDenseExactExchangeFamily g y B leaf J ∧
      ((∃ hRne : ∀ i, R i ≠ i,
          TwoRetainedPivotAlignedDensePrimitiveComponentCRTStateFamily
            g y (h + g r) B leaf center P J R hRne) ∨
        d + 2 ≤ m + 1))

/-- Install the CRT state in HBK's terminal without changing any other
branch. -/
theorem twoRetainedPivotAlignedDensePrimitiveComponentCRTTerminal_of_exactOrderTerminal
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (y : ZMod (2 ^ 5 * q)) (B : Finset (Fin (m + 1)))
    {d : ℕ} (leaf center : Fin d → Fin (m + 1))
    (P : Equiv.Perm (Fin d)) (J : Finset (Fin d))
    (R : Equiv.Perm (Fin d))
    (hterminal :
      TwoRetainedPivotAlignedDensePrimitiveComponentExactOrderTerminal
        g h r y B leaf center P J R) :
    TwoRetainedPivotAlignedDensePrimitiveComponentCRTTerminal
      g h r y B leaf center P J R := by
  rcases hterminal with hproper | hshrink | hexact
  · exact Or.inl hproper
  · exact Or.inr (Or.inl hshrink)
  · rcases hexact with
      ⟨hfullOdd, hcapacity, hexchange, ⟨hRne, hcomponent⟩ | hcapacityOld⟩
    · exact Or.inr (Or.inr
        ⟨hfullOdd, hcapacity, hexchange,
          Or.inl ⟨hRne, hcomponent.componentCRT
            g y (h + g r) B leaf center P J R hRne⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hfullOdd, hcapacity, hexchange, Or.inr hcapacityOld⟩)

/-- Public C2 endpoint carrying the exact CRT scalar gcds, sharp target
orders, and the critical four-coordinate margin. -/
def PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentCRTOutcome
    {q : ℕ} (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    (h : ZMod (2 ^ 5 * q)) (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    (a : ↥(witnessPureEdgeStarLeaves g h r)) (d : ℕ)
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ) : Prop :=
  let leaf : Fin d → Fin (m + 1) :=
    fun j ↦ (T^[j.val] a : Fin (m + 1))
  let disp : Fin d → ZMod (2 ^ 5 * q) :=
    fun j ↦ g (leaf j) - (h + g r)
  2 * d + 1 ≤ m + 1 ∨
    (d + 2 ≤ m + 1 ∧
      ∃ j k ell : Fin d,
        center j = leaf k ∧ center ell ∉ Set.range leaf) ∨
    (PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome
        g h r T a d center ∧
      ∃ y : ZMod (2 ^ 5 * q), ∃ B : Finset (Fin (m + 1)),
        ∃ P : Equiv.Perm (Fin d), ∃ J : Finset (Fin d),
          AddSubgroup.closure (Set.range disp) =
            AddSubgroup.zmultiples y ∧
          (∀ j : Fin d, disp j ∈ AddSubgroup.zmultiples y) ∧
          OddPrimaryFullCycleRetainedExternalChargeDescent
            g y B d leaf ∧
          CycleCenterSparseKernelPrivateWitnessFamily
            g y B leaf center P J ∧
          CycleCenterSparseRetainedExternalOrArithmeticPivotStar
            g y B center P J ∧
          CycleCenterSparseRetainedExternalOrCommonPivot
            g y B center P J ∧
          RetainedExternalInternalRowPartition
            g y B center P J ∧
          ∃ S : Equiv.Perm (Fin d),
            (∀ j : Fin d,
              P j ≠ j ∧ P j ≠ S j ∧
              center j = leaf (P j) ∧
              (T (T^[j.val] a) : Fin (m + 1)) = leaf (S j) ∧
              (2 : ℤ) • g (leaf (P j)) =
                h + g r + g (leaf (S j))) ∧
            (∀ j : Fin d,
              disp ((P.symm.trans S) j) = 2 • disp j) ∧
            (2 < m + 1 - B.card ∨
              (TwoRetainedMinimalCyclicKernelPrivateRows g y B ∧
                TwoRetainedMinimalCyclicKernelFiveWeightRows g y B ∧
                ((∀ j : Fin d, leaf j ∈ B) ∨
                  ∃ p : Fin d, ∀ j : Fin d, leaf j ∈ B ↔ j ≠ p) ∧
                (TwoRetainedPivotAlignedDensePrimitiveComponentCRTTerminal
                    g h r y B leaf center P J (P.symm.trans S) ∨
                  TwoRetainedDominantExternalCycleComponentArm
                    g y (h + g r) B center P J (P.symm.trans S)
                      componentThreshold))))

/-- Upgrade the exact-order endpoint with its exact scalar-gcd CRT
projection. -/
theorem pureEdgeStarLeafCycle_c2DensePrimitiveComponentCRTOutcome_of_exactOrderOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q))
    {h : ZMod (2 ^ 5 * q)} (r : Fin (m + 1))
    (T : ↥(witnessPureEdgeStarLeaves g h r) →
      ↥(witnessPureEdgeStarLeaves g h r))
    {a : ↥(witnessPureEdgeStarLeaves g h r)} {d : ℕ}
    (center : Fin d → Fin (m + 1)) (componentThreshold : ℕ)
    (hout :
      PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentExactOrderOutcome
        g h r T a d center componentThreshold) :
    PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentCRTOutcome
      g h r T a d center componentThreshold := by
  rcases hout with hcap | hmixed |
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        harithmetic, hnormal, hpartition, S, hlocal, hdouble,
        hthree | hexact⟩
  · exact Or.inl hcap
  · exact Or.inr (Or.inl hmixed)
  · exact Or.inr (Or.inr
      ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
        harithmetic, hnormal, hpartition, S, hlocal, hdouble,
        Or.inl hthree⟩)
  · rcases hexact with
      ⟨hprivate, hfive, hleafSplit, hterminal | hexternal⟩
    · have hterminal' :=
        twoRetainedPivotAlignedDensePrimitiveComponentCRTTerminal_of_exactOrderTerminal
          g h r y B
            (fun j ↦ (T^[j.val] a : Fin (m + 1))) center P J
              (P.symm.trans S) hterminal
      exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inl hterminal'⟩⟩)
    · exact Or.inr (Or.inr
        ⟨hcharge, y, B, P, J, hspan, hmem, hretained, hsparse,
          harithmetic, hnormal, hpartition, S, hlocal, hdouble,
          Or.inr ⟨hprivate, hfive, hleafSplit, Or.inr hexternal⟩⟩)

/-- Global minimal-counterexample constructor with exact scalar gcds for the
cross-component common-pivot rows. -/
theorem exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentCRTOutcome
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin (m + 1) → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound (m + 1) 5)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple (m + 1) M)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hno : ¬ ∃ z : Fin (m + 1), ∀ c : Fin (m + 1) → ℤ,
      Witness g h c → c z ≠ 0)
    (r : Fin (m + 1))
    (qroot : ReducedSubsetSumCollision g h)
    (hqCanonical : qroot ∈ canonicalReducedCollisions (g := g) hh)
    (hcoeff : subsetCollisionCoeffs qroot.val.1 qroot.val.2 =
        supportAvoidingWitnessAt g hno r ∨
      subsetCollisionCoeffs qroot.val.1 qroot.val.2 =
        -supportAvoidingWitnessAt g hno r)
    (hthree : ¬ WitnessThreeDistinctOmissions g h)
    (hcross : ∀ q' : ReducedSubsetSumCollision g h,
      ¬ ((qroot, q') ∈ canonicalPositiveNegativeCrossPairs (g := g) hh ∨
        (q', qroot) ∈ canonicalPositiveNegativeCrossPairs (g := g) hh))
    (hL : (witnessPureEdgeStarLeaves g h r).Nonempty)
    (componentThreshold : ℕ) :
    ∃ T : ↥(witnessPureEdgeStarLeaves g h r) →
        ↥(witnessPureEdgeStarLeaves g h r),
      ∃ a : ↥(witnessPureEdgeStarLeaves g h r), ∃ d : ℕ,
        ∃ center : Fin d → Fin (m + 1),
          d ≤ (witnessPureEdgeStarLeaves g h r).card ∧
          IsMinimalFixedPointFreeCycle T a d ∧
          Function.Injective center ∧
          (∀ j : Fin d,
            center j ≠ r ∧
            center j ≠ (T^[j.val] a : Fin (m + 1)) ∧
            center j ≠ (T (T^[j.val] a) : Fin (m + 1)) ∧
            (2 : ℤ) • g (center j) =
              h + g r + g (T (T^[j.val] a) : Fin (m + 1))) ∧
          PureEdgeStarLeafOddPrimaryFullCycleC2DensePrimitiveComponentCRTOutcome
            g h r T a d center componentThreshold := by
  obtain ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout⟩ :=
    exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleC2DensePrimitiveComponentExactOrderOutcome
      g hg hcritical hminimal hh hne hno r qroot hqCanonical hcoeff hthree
        hcross hL componentThreshold
  have hout' :=
    pureEdgeStarLeafCycle_c2DensePrimitiveComponentCRTOutcome_of_exactOrderOutcome
      g r T center componentThreshold hout
  exact ⟨T, a, d, center, hdCard, hTcycle, hcenter, hcenterSpec, hout'⟩

end MinModulus
