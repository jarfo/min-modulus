/-
# Uniform positive-stratum exchange

The complete quotient normal form exposes a deleted owner of full quotient
order in every non-full retained-difference arm, including the formerly
degenerate first stratum.  Exchange that owner with one retained coordinate
and minimize the resulting cyclic-kernel transversal.

A strict minimization enters the already separated three-retained C2 branch.
Otherwise the literal exchanged set remains minimal, has two retained
coordinates with quotient difference of order `2^t`, and inherits the exact
two-lift row normal form.  Thus no positive stratum needs a separate exchange
argument.
-/
import MinModulus.G1OddPrimaryFullCyclePositiveStratumQuotientPhase
import MinModulus.G1OddPrimaryFullCycleTransversalExchange
import MinModulus.G1OddPrimaryFullCyclePrimitiveUnitRows

namespace MinModulus

open Finset

variable {n : ℕ}

/-- A weight-`-1` owner primitive relative to `z` is equally primitive
relative to `x`: its row says that the retained difference is twice the
owner displacement, so the second displacement is its negative. -/
theorem TwoRetainedFiveWeightPresentation.primitive_otherRetained_of_weight_eq_neg_one
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (b : ↥B) (hweight : p.weight b = -1)
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g (b : Fin n) - g p.z)) = 2 ^ t) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    addOrderOf (pi (g (b : Fin n) - g p.x)) = 2 ^ t := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  have hquotientRelation :
      (2 : ℤ) • betaQ + p.weight b • deltaQ = 0 := by
    apply (QuotientAddGroup.eq_zero_iff
      ((2 : ℤ) • (g (b : Fin n) - g p.z) +
        p.weight b • (g p.x - g p.z))).mpr
    exact p.row_mem b
  have hdeltaDouble : deltaQ = (2 : ℕ) • betaQ := by
    rw [hweight] at hquotientRelation
    change (2 : ℤ) • betaQ + (-1 : ℤ) • deltaQ = 0 at hquotientRelation
    have hrelation' : betaQ + betaQ - deltaQ = 0 := by
      simpa only [two_zsmul, neg_one_zsmul, sub_eq_add_neg] using
        hquotientRelation
    calc
      deltaQ = (betaQ + betaQ - deltaQ) + deltaQ := by
        rw [hrelation', zero_add]
      _ = betaQ + betaQ := by abel
      _ = (2 : ℕ) • betaQ := (two_nsmul betaQ).symm
  have hdecomp :
      g (b : Fin n) - g p.x =
        (g (b : Fin n) - g p.z) - (g p.x - g p.z) := by
    abel
  have hquotient : pi (g (b : Fin n) - g p.x) = -betaQ := by
    rw [hdecomp, map_sub]
    change betaQ - deltaQ = -betaQ
    rw [hdeltaDouble]
    module
  change addOrderOf (pi (g (b : Fin n) - g p.x)) = 2 ^ t
  rw [hquotient, addOrderOf_neg]
  simpa only [betaQ, pi, H, Q] using hprimitive

/-- Exchanging an owner outside a one-missing-leaf range for that missing
leaf puts the entire range into the exchanged deletion set. -/
theorem cycleRange_subset_insert_erase_missing
    {d : ℕ} (leaf : Fin d → Fin n) (p : Fin d)
    {B : Finset (Fin n)} {b x : Fin n}
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hmissing : leaf p = x) (hbOutside : b ∉ Set.range leaf) :
    ∀ i, leaf i ∈ insert x (B.erase b) := by
  classical
  intro i
  by_cases hip : i = p
  · subst i
    rw [hmissing]
    exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    apply Finset.mem_erase.mpr
    refine ⟨?_, (hleafB i).2 hip⟩
    intro hleafb
    exact hbOutside ⟨i, hleafb⟩

/-- Exchanging one deleted cycle leaf for a point outside the cycle leaves
exactly that leaf undeleted. -/
theorem cycleRange_mem_insert_erase_leaf_iff
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    {B : Finset (Fin n)} (hleafB : ∀ i, leaf i ∈ B)
    (r : Fin d) {x : Fin n} (hxOutside : x ∉ Set.range leaf) :
    ∀ i, leaf i ∈ insert x (B.erase (leaf r)) ↔ i ≠ r := by
  classical
  intro i
  constructor
  · intro hi hir
    subst i
    simp only [Finset.mem_insert, Finset.mem_erase] at hi
    rcases hi with hxr | hir
    · exact hxOutside ⟨r, hxr⟩
    · exact hir.1 rfl
  · intro hir
    apply Finset.mem_insert_of_mem
    apply Finset.mem_erase.mpr
    refine ⟨?_, hleafB i⟩
    intro hleafEq
    exact hir (hleafInj hleafEq)

/-- Literal exchanges of distinct injective cycle leaves give distinct
deletion sets when the inserted point was not deleted originally. -/
theorem insert_erase_cycleLeaf_injective
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    {B : Finset (Fin n)} (hleafB : ∀ i, leaf i ∈ B)
    {x : Fin n} (hxB : x ∉ B) :
    Function.Injective (fun r ↦ insert x (B.erase (leaf r))) := by
  classical
  intro r s hrs
  change insert x (B.erase (leaf r)) = insert x (B.erase (leaf s)) at hrs
  apply hleafInj
  by_contra hleafNe
  have hmemRight : leaf r ∈ insert x (B.erase (leaf s)) := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_erase.mpr ⟨hleafNe, hleafB r⟩
  have hmemLeft : leaf r ∈ insert x (B.erase (leaf r)) := by
    rw [hrs]
    exact hmemRight
  simp only [Finset.mem_insert, Finset.mem_erase] at hmemLeft
  rcases hmemLeft with hleafX | hfalse
  · exact hxB (hleafX ▸ hleafB r)
  · exact hfalse.1 rfl

/-- A cycle whose translated displacements span the cyclic kernel has one
quotient coset: all leaf displacements from any fixed base have the same
image modulo that kernel. -/
theorem cycle_quotient_displacement_eq_of_span
    {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (y a base : G)
    {d : ℕ} (leaf : Fin d → Fin n)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    let H := AddSubgroup.zmultiples y
    let pi : G →+ G ⧸ H := QuotientAddGroup.mk' H
    ∀ i j,
      pi (g (leaf i) - base) = pi (g (leaf j) - base) := by
  let H : AddSubgroup G := AddSubgroup.zmultiples y
  let pi : G →+ G ⧸ H := QuotientAddGroup.mk' H
  change ∀ i j,
    pi (g (leaf i) - base) = pi (g (leaf j) - base)
  intro i j
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (QuotientAddGroup.eq_zero_iff
    ((g (leaf i) - base) - (g (leaf j) - base))).mpr
  have hi : g (leaf i) - a ∈ H := by
    change g (leaf i) - a ∈ AddSubgroup.zmultiples y
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  have hj : g (leaf j) - a ∈ H := by
    change g (leaf j) - a ∈ AddSubgroup.zmultiples y
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨j, rfl⟩
  have hij := H.sub_mem hi hj
  have heq :
      (g (leaf i) - base) - (g (leaf j) - base) =
        (g (leaf i) - a) - (g (leaf j) - a) := by
    abel
  rw [heq]
  exact hij

/-- Reverse the retained orientation of one five-weight presentation.  The
normalized weight transforms by `w ↦ -2-w`, leaving the underlying affine
row unchanged. -/
def TwoRetainedFiveWeightPresentation.reverse
    {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedFiveWeightPresentation g y B) :
    TwoRetainedFiveWeightPresentation g y B where
  x := p.z
  z := p.x
  weight := fun b ↦ -2 - p.weight b
  x_not_mem := p.z_not_mem
  z_not_mem := p.x_not_mem
  x_ne_z := p.x_ne_z.symm
  complement_eq := by simpa only [pair_comm] using p.complement_eq
  weight_mem := by
    intro b
    have hb := p.weight_mem b
    simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
      Finset.mem_singleton] at hb ⊢
    rcases hb with hb | hb | hb | hb | hb <;> omega
  row_mem := by
    intro b
    have hb := p.row_mem b
    convert hb using 1
    module

/-- Extract a five-weight presentation in either prescribed ordering of the
two retained coordinates. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.fiveWeightPresentation_with_orientation
    {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z) :
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      p.x = x ∧ p.z = z := by
  classical
  obtain ⟨p⟩ := hrows.fiveWeightPresentation g y B
  have hxComplement : x ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxB⟩
  have hzComplement : z ∈ Finset.univ \ B :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩
  rw [p.complement_eq] at hxComplement hzComplement
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxComplement hzComplement
  rcases hxComplement with hxpX | hxpZ
  · have hzpZ : z = p.z := hzComplement.resolve_left (by
      intro hzpX
      exact hxz (hxpX.trans hzpX.symm))
    exact ⟨p, hxpX.symm, hzpZ.symm⟩
  · have hzpX : z = p.x := hzComplement.resolve_right (by
      intro hzpZ
      exact hxz (hxpZ.trans hzpZ.symm))
    refine ⟨p.reverse g y B, ?_, ?_⟩
    · exact hxpZ.symm
    · exact hzpX.symm

/-- The full-order two-retained state after positive-stratum exchange. -/
def PrimitiveTwoRetainedPositiveStratumRows
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n)) : Prop :=
  MinimalCyclicKernelSupportTransversal g y B ∧
    n - B.card = 2 ∧
    TwoRetainedMinimalCyclicKernelFiveWeightRows g y B ∧
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      let deltaQ := pi (g p.x - g p.z)
      addOrderOf deltaQ = 2 ^ t ∧
        ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
          (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
            pi (g (b : Fin n) - g p.z) =
              (2 ^ (t - 1) : ℕ) • deltaQ - k • deltaQ)

/-- A full-order positive-stratum state with its exact row presentation kept
as explicit data.  This carrier prevents later cycle arguments from choosing
a second, potentially oppositely oriented presentation. -/
def PrimitiveTwoRetainedPositiveStratumPresentation
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n))
    (p : TwoRetainedFiveWeightPresentation g y B) : Prop :=
  MinimalCyclicKernelSupportTransversal g y B ∧
    n - B.card = 2 ∧
    TwoRetainedMinimalCyclicKernelFiveWeightRows g y B ∧
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    let deltaQ := pi (g p.x - g p.z)
    addOrderOf deltaQ = 2 ^ t ∧
      ∀ b : ↥B, ∃ k : ℤ, p.weight b = 2 * k ∧
        (pi (g (b : Fin n) - g p.z) = -(k • deltaQ) ∨
          pi (g (b : Fin n) - g p.z) =
            (2 ^ (t - 1) : ℕ) • deltaQ - k • deltaQ)

/-- The existential state is exactly the existence of one explicit
presentation carrier. -/
theorem primitiveTwoRetainedPositiveStratumRows_iff_exists_presentation
    {t q : ℕ} (g : Fin n → ZMod (2 ^ t * q))
    (y : ZMod (2 ^ t * q)) (B : Finset (Fin n)) :
    PrimitiveTwoRetainedPositiveStratumRows g y B ↔
      ∃ p : TwoRetainedFiveWeightPresentation g y B,
        PrimitiveTwoRetainedPositiveStratumPresentation g y B p := by
  constructor
  · rintro ⟨hmin, hretained, hrows, p, hp⟩
    exact ⟨p, hmin, hretained, hrows, hp⟩
  · rintro ⟨p, hmin, hretained, hrows, hp⟩
    exact ⟨hmin, hretained, hrows, p, hp⟩

/-- Reorient a full-order state by any prescribed ordering of its two
retained coordinates while preserving the intrinsic quotient order. -/
theorem PrimitiveTwoRetainedPositiveStratumRows.exists_fullOrderPresentation_with_orientation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedPositiveStratumRows g y B)
    (x z : Fin n) (hxB : x ∉ B) (hzB : z ∉ B) (hxz : x ≠ z) :
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      p.x = x ∧ p.z = z ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) = 2 ^ t := by
  classical
  rcases hstate with ⟨_hmin, _hretained, hrows, p₀, hp₀full⟩
  obtain ⟨p, hpx, hpz⟩ :=
    hrows.fiveWeightPresentation_with_orientation
      g y B x z hxB hzB hxz
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  have hp₀Order : addOrderOf (pi (g p₀.x - g p₀.z)) = 2 ^ t := by
    simpa only [pi, H, Q] using hp₀full.1
  have hxCase : x = p₀.x ∨ x = p₀.z := by
    have hxMem : x ∈ Finset.univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxB⟩
    rw [p₀.complement_eq] at hxMem
    simpa using hxMem
  have hzCase : z = p₀.x ∨ z = p₀.z := by
    have hzMem : z ∈ Finset.univ \ B :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩
    rw [p₀.complement_eq] at hzMem
    simpa using hzMem
  have hxzOrder : addOrderOf (pi (g x - g z)) = 2 ^ t := by
    rcases hxCase with hxpX | hxpZ
    · have hzpZ : z = p₀.z := hzCase.resolve_left (by
        intro hzpX
        exact hxz (hxpX.trans hzpX.symm))
      simpa only [hxpX, hzpZ] using hp₀Order
    · have hzpX : z = p₀.x := hzCase.resolve_right (by
        intro hzpZ
        exact hxz (hxpZ.trans hzpZ.symm))
      have hneg : g x - g z = -(g p₀.x - g p₀.z) := by
        rw [hxpZ, hzpX]
        abel
      rw [hneg, map_neg, addOrderOf_neg]
      exact hp₀Order
  refine ⟨p, hpx, hpz, ?_⟩
  rw [hpx, hpz]
  simpa only [pi, H, Q] using hxzOrder

/-- An odd integer multiple of an element of order `2^t` has the same order.
This is the parity fact that makes the positive-stratum exchange orientation
uniform. -/
theorem addOrderOf_odd_zsmul_eq_twoPower
    {Q : Type*} [AddCommGroup Q] [Finite Q]
    {t : ℕ} (delta : Q) (hdelta : addOrderOf delta = 2 ^ t)
    (c : ℤ) (hc : Odd c) :
    addOrderOf (c • delta) = 2 ^ t := by
  rcases Int.eq_nat_or_neg c with ⟨k, rfl | rfl⟩
  · have hkOdd : Odd k := by exact_mod_cast hc
    have hcoprime : (2 ^ t).Coprime k :=
      hkOdd.coprime_two_left.pow_left t
    rw [natCast_zsmul, addOrderOf_nsmul, hdelta,
      hcoprime.gcd_eq_one, Nat.div_one]
  · have hkOdd : Odd k := by simpa using hc
    have hcoprime : (2 ^ t).Coprime k :=
      hkOdd.coprime_two_left.pow_left t
    rw [neg_zsmul, addOrderOf_neg, natCast_zsmul, addOrderOf_nsmul,
      hdelta, hcoprime.gcd_eq_one, Nat.div_one]

/-- If `beta` is any integer multiple of a primitive `2^t`-element, then
`beta` or `beta-delta` is primitive: their integer coefficients are
consecutive, hence one is odd. -/
theorem addOrderOf_eq_twoPower_or_sub_eq_twoPower_of_eq_zsmul
    {Q : Type*} [AddCommGroup Q] [Finite Q]
    {t : ℕ} (delta beta : Q) (hdelta : addOrderOf delta = 2 ^ t)
    (c : ℤ) (hbeta : beta = c • delta) :
    addOrderOf beta = 2 ^ t ∨ addOrderOf (beta - delta) = 2 ^ t := by
  rcases Int.even_or_odd c with hc | hc
  · right
    have hcSub : Odd (c - 1) := hc.sub_odd odd_one
    have hsub : beta - delta = (c - 1) • delta := by
      rw [hbeta]
      module
    rw [hsub]
    exact addOrderOf_odd_zsmul_eq_twoPower delta hdelta (c - 1) hcSub
  · left
    rw [hbeta]
    exact addOrderOf_odd_zsmul_eq_twoPower delta hdelta c hc

/-- Every deleted owner in an exact full-order presentation is primitive
relative to at least one of the two retained coordinates.  The exact row
normal form puts its quotient displacement in `Z*delta`; switching the
retained base point subtracts one copy of `delta`. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.owner_primitive_at_one_retained
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (b : ↥B) :
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
      QuotientAddGroup.mk' H
    addOrderOf (pi (g (b : Fin n) - g p.z)) = 2 ^ t ∨
      addOrderOf (pi (g (b : Fin n) - g p.x)) = 2 ^ t := by
  rcases hpres with ⟨_hmin, _hretained, _hrows, hfull⟩
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  let betaQ : Q := pi (g (b : Fin n) - g p.z)
  have hdelta : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, pi, H, Q] using hfull.1
  obtain ⟨k, _hweight, hbeta | hbeta⟩ := hfull.2 b
  · have hmultiple : betaQ = (-k) • deltaQ := by
      simpa only [betaQ, deltaQ, pi, H, Q, neg_zsmul] using hbeta
    have hprimitive :=
      addOrderOf_eq_twoPower_or_sub_eq_twoPower_of_eq_zsmul
        deltaQ betaQ hdelta (-k) hmultiple
    have hbaseChange :
        pi (g (b : Fin n) - g p.x) = betaQ - deltaQ := by
      have hvalue :
          g (b : Fin n) - g p.x =
            (g (b : Fin n) - g p.z) - (g p.x - g p.z) := by
        abel
      rw [hvalue, map_sub]
    simpa only [betaQ, deltaQ, pi, H, Q, hbaseChange] using hprimitive
  · have hmultiple :
        betaQ = ((2 ^ (t - 1) : ℕ) : ℤ) • deltaQ - k • deltaQ := by
      simpa only [betaQ, deltaQ, pi, H, Q, natCast_zsmul] using hbeta
    have hmultiple' :
        betaQ = (((2 ^ (t - 1) : ℕ) : ℤ) - k) • deltaQ := by
      rw [hmultiple]
      module
    have hprimitive :=
      addOrderOf_eq_twoPower_or_sub_eq_twoPower_of_eq_zsmul
        deltaQ betaQ hdelta (((2 ^ (t - 1) : ℕ) : ℤ) - k) hmultiple'
    have hbaseChange :
        pi (g (b : Fin n) - g p.x) = betaQ - deltaQ := by
      have hvalue :
          g (b : Fin n) - g p.x =
            (g (b : Fin n) - g p.z) - (g p.x - g p.z) := by
        abel
      rw [hvalue, map_sub]
    simpa only [betaQ, deltaQ, pi, H, Q, hbaseChange] using hprimitive

/-- Full quotient order makes the five-weight labels of a fully deleted
doubling cycle constant in the *given* row presentation.  This is the
presentation-preserving version of the generic cycle split: the alternative
nonzero coefficient has absolute value at most `18`, while full order forces
its absolute value to be divisible by `2^t`. -/
theorem TwoRetainedFiveWeightPresentation.fullDeleted_weight_constant_of_fullOrder
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hfull :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g p.x - g p.z)) = 2 ^ t)
    (hpow : 18 < 2 ^ t)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ t * q))
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∀ i j,
      p.weight ⟨leaf i, hleafB i⟩ = p.weight ⟨leaf j, hleafB j⟩ := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) :=
    AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let delta : ZMod (2 ^ t * q) := g p.x - g p.z
  let deltaQ : Q := pi delta
  have hdeltaOrder : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, delta, pi, H, Q] using hfull
  have htransition : ∀ i,
      (p.weight ⟨leaf (R i), hleafB (R i)⟩ -
          2 * p.weight ⟨leaf i, hleafB i⟩) • delta +
        (2 : ℤ) • (g p.z - a) ∈ H := by
    intro i
    have hsub := H.sub_mem (p.row_mem ⟨leaf (R i), hleafB (R i)⟩)
      (H.zsmul_mem (p.row_mem ⟨leaf i, hleafB i⟩) 2)
    have hvalue :
        g (leaf (R i)) = (2 : ℤ) • g (leaf i) - a := by
      calc
        g (leaf (R i)) = (g (leaf (R i)) - a) + a := by abel
        _ = (2 : ℤ) • (g (leaf i) - a) + a := by rw [hdouble i]
        _ = (2 : ℤ) • g (leaf i) - a := by module
    convert hsub using 1
    dsimp only [H, delta]
    rw [hvalue]
    module
  have hpair : ∀ i j,
      ((p.weight ⟨leaf (R i), hleafB (R i)⟩ -
          2 * p.weight ⟨leaf i, hleafB i⟩) -
        (p.weight ⟨leaf (R j), hleafB (R j)⟩ -
          2 * p.weight ⟨leaf j, hleafB j⟩)) • delta ∈ H := by
    intro i j
    have hsub := H.sub_mem (htransition i) (htransition j)
    convert hsub using 1
    module
  let cycleWeight : Fin d → ℤ := fun i ↦
    p.weight ⟨leaf i, hleafB i⟩
  let i₀ : Fin d := ⟨0, hd⟩
  have hcycleWeight : ∀ i,
      cycleWeight i ∈ twoRetainedNormalizedWeightLevels := by
    intro i
    exact p.weight_mem ⟨leaf i, hleafB i⟩
  have hcyclePair : ∀ i j,
      ((cycleWeight (R i) - 2 * cycleWeight i) -
        (cycleWeight (R j) - 2 * cycleWeight j)) • delta ∈ H := by
    intro i j
    simpa only [cycleWeight] using hpair i j
  rcases fiveWeightTransition_smallKernelMultiple_or_weight_constant
      i₀ R cycleWeight hcycleWeight delta y hcyclePair with
    ⟨e, he, helow, hehigh, heMem⟩ | hconstant
  · have heQuotient : e • deltaQ = 0 := by
      apply (QuotientAddGroup.eq_zero_iff (e • delta)).mpr
      simpa only [H] using heMem
    have hnatQuotient : e.natAbs • deltaQ = 0 := by
      rw [← natCast_zsmul]
      rcases Int.natAbs_eq e with hePos | heNeg
      · rw [hePos] at heQuotient
        exact heQuotient
      · rw [heNeg, neg_smul] at heQuotient
        exact neg_eq_zero.mp heQuotient
    have horderDvd : 2 ^ t ∣ e.natAbs := by
      rw [← hdeltaOrder]
      exact addOrderOf_dvd_of_nsmul_eq_zero hnatQuotient
    have horderLe : 2 ^ t ≤ e.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr he) horderDvd
    have habsLe : e.natAbs ≤ 18 := by
      rcases Int.natAbs_eq e with hePos | heNeg
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
    omega
  · simpa only [cycleWeight] using hconstant

/-- In a presentation oriented with the unique retained cycle leaf first,
full quotient order forces every deleted cycle-leaf row to have pure weight
`-2`.  Only the common cycle coset and the order gap `4 < 2^t` are used. -/
theorem TwoRetainedFiveWeightPresentation.oneRetainedCycle_weight_eq_neg_two_of_fullOrder
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hfull :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 2 ^ t)
    (hpow : 4 < 2 ^ t)
    {d : ℕ} (leaf : Fin d → Fin n) (a : ZMod (2 ^ t * q))
    (r : Fin d) (hpx : leaf r = p.x)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    ∀ i (hi : leaf i ∈ B), p.weight ⟨leaf i, hi⟩ = -2 := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g p.x - g p.z)
  have hdelta : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, pi, H, Q] using hfull
  intro i hi
  have hbeta : pi (g (leaf i) - g p.z) = deltaQ := by
    calc
      pi (g (leaf i) - g p.z) = pi (g (leaf r) - g p.z) :=
        cycle_quotient_displacement_eq_of_span
          g y a (g p.z) leaf hspan i r
      _ = deltaQ := by rw [hpx]
  have hquotientRelation :
      (2 : ℤ) • pi (g (leaf i) - g p.z) +
        p.weight ⟨leaf i, hi⟩ • deltaQ = 0 := by
    apply (QuotientAddGroup.eq_zero_iff
      ((2 : ℤ) • (g (leaf i) - g p.z) +
        p.weight ⟨leaf i, hi⟩ • (g p.x - g p.z))).mpr
    exact p.row_mem ⟨leaf i, hi⟩
  rw [hbeta] at hquotientRelation
  let e : ℤ := p.weight ⟨leaf i, hi⟩ + 2
  have heZero : e • deltaQ = 0 := by
    dsimp only [e]
    rw [add_zsmul]
    rw [add_comm]
    exact hquotientRelation
  by_contra hweight
  have he : e ≠ 0 := by
    intro he
    apply hweight
    dsimp only [e] at he
    omega
  have hnatZero : e.natAbs • deltaQ = 0 := by
    rw [← natCast_zsmul]
    rcases Int.natAbs_eq e with hePos | heNeg
    · rw [hePos] at heZero
      exact heZero
    · rw [heNeg, neg_smul] at heZero
      exact neg_eq_zero.mp heZero
  have horderDvd : 2 ^ t ∣ e.natAbs := by
    rw [← hdelta]
    exact addOrderOf_dvd_of_nsmul_eq_zero hnatZero
  have horderLe : 2 ^ t ≤ e.natAbs :=
    Nat.le_of_dvd (Int.natAbs_pos.mpr he) horderDvd
  have hweightMem := p.weight_mem ⟨leaf i, hi⟩
  have habsLe : e.natAbs ≤ 4 := by
    simp only [twoRetainedNormalizedWeightLevels, Finset.mem_insert,
      Finset.mem_singleton] at hweightMem
    rcases Int.natAbs_eq e with hePos | heNeg
    · have : (e.natAbs : ℤ) ≤ 4 := by
        dsimp only [e]
        rcases hweightMem with hw | hw | hw | hw | hw <;> omega
      exact_mod_cast this
    · have : (e.natAbs : ℤ) ≤ 4 := by
        dsimp only [e]
        rcases hweightMem with hw | hw | hw | hw | hw <;> omega
      exact_mod_cast this
  omega

/-- A punctured-cycle full-order state in the common comparison orientation:
the missing leaf is retained first, a fixed off-cycle endpoint is retained
second, and every surviving cycle leaf has pure normalized weight `-2`. -/
def PrimitiveOneRetainedCyclePurePresentation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n)) {d : ℕ} (leaf : Fin d → Fin n)
    (r : Fin d) (z : Fin n) : Prop :=
  PrimitiveTwoRetainedPositiveStratumRows g y B ∧
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      p.x = leaf r ∧ p.z = z ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) = 2 ^ t ∧
        ∀ i (hi : leaf i ∈ B), p.weight ⟨leaf i, hi⟩ = -2

/-- Put one punctured-cycle full-order state into the common pure comparison
orientation. -/
theorem PrimitiveTwoRetainedPositiveStratumRows.to_oneRetainedCyclePurePresentation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedPositiveStratumRows g y B)
    (hpow : 4 < 2 ^ t)
    {d : ℕ} (leaf : Fin d → Fin n) (a : ZMod (2 ^ t * q))
    (r : Fin d) (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ r)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (z : Fin n) (hzB : z ∉ B) (hrz : leaf r ≠ z) :
    PrimitiveOneRetainedCyclePurePresentation g y B leaf r z := by
  have hrB : leaf r ∉ B := by
    rw [hleafB r]
    simp
  obtain ⟨p, hpx, hpz, hfull⟩ :=
    hstate.exists_fullOrderPresentation_with_orientation
      g y B (leaf r) z hrB hzB hrz
  refine ⟨hstate, p, hpx, hpz, hfull, ?_⟩
  exact p.oneRetainedCycle_weight_eq_neg_two_of_fullOrder
    g y B hfull hpow leaf a r hpx.symm hspan

/-- Canonical private-row data for every member of a simultaneous punctured
cycle family.  Besides the aligned presentations, the carrier keeps the
literal deletion sets, cycle incidence, both relevant full-order differences,
and the common inserted owner in every transversal. -/
structure PrimitivePuncturedCyclePrivateMatrix
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    {d : ℕ} (set : Fin d → Finset (Fin n)) (leaf : Fin d → Fin n)
    (inserted fixed : Fin n) where
  state : ∀ r, PrimitiveTwoRetainedPositiveStratumRows g y (set r)
  presentation : ∀ r,
    TwoRetainedCanonicalPrivatePresentation g y (set r)
  leaf_injective : Function.Injective leaf
  common_mem : ∀ r, inserted ∈ set r
  leaf_mem_iff : ∀ r i, leaf i ∈ set r ↔ i ≠ r
  missing_first : ∀ r, (presentation r).x = leaf r
  fixed_second : ∀ r, (presentation r).z = fixed
  retained_full_order : ∀ r,
    addOrderOf
      ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
        (g (presentation r).x - g (presentation r).z)) = 2 ^ t
  common_full_order :
    addOrderOf
      ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
        (g inserted - g fixed)) = 2 ^ t
  surviving_weight : ∀ r i (hi : leaf i ∈ set r),
    (presentation r).weight ⟨leaf i, hi⟩ = -2
  set_injective : Function.Injective set

/-- Reconstruct the canonical private witnesses in the same pure orientation
as one punctured state. -/
theorem PrimitiveOneRetainedCyclePurePresentation.exists_canonicalPrivatePresentation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) (a : ZMod (2 ^ t * q))
    (r : Fin d) (z : Fin n)
    (hpure : PrimitiveOneRetainedCyclePurePresentation g y B leaf r z)
    (hpow : 4 < 2 ^ t)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
      p.x = leaf r ∧ p.z = z ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) = 2 ^ t ∧
        ∀ i (hi : leaf i ∈ B), p.weight ⟨leaf i, hi⟩ = -2 := by
  classical
  rcases hpure with ⟨hstate, p₀, hp₀x, hp₀z, hp₀full, _hp₀weight⟩
  have hrB : leaf r ∉ B := by
    simpa only [← hp₀x] using p₀.x_not_mem
  have hzB : z ∉ B := by
    simpa only [← hp₀z] using p₀.z_not_mem
  have hrz : leaf r ≠ z := by
    intro hrz
    apply p₀.x_ne_z
    rw [hp₀x, hp₀z, hrz]
  have hcomplement : Finset.univ \ B = {leaf r, z} := by
    simpa only [hp₀x, hp₀z] using p₀.complement_eq
  obtain ⟨p, hpx, hpz⟩ :=
    exists_twoRetainedCanonicalPrivatePresentation
      g y hstate.1 hstate.2.1 (leaf r) z hrB hzB hrz hcomplement
  have hfull :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 2 ^ t := by
    simpa only [hpx, hpz, hp₀x, hp₀z] using hp₀full
  let pFive := p.toFiveWeightPresentation g y B
  have hweight :=
    pFive.oneRetainedCycle_weight_eq_neg_two_of_fullOrder
      g y B hfull hpow leaf a r hpx.symm hspan
  refine ⟨p, hpx, hpz, hfull, ?_⟩
  intro i hi
  simpa only [pFive,
    TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation] using
      hweight i hi

/-- Assemble canonical private presentations pointwise from an aligned pure
punctured family. -/
theorem exists_primitivePuncturedCyclePrivateMatrix_of_pureFamily
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    {d : ℕ} (set : Fin d → Finset (Fin n)) (leaf : Fin d → Fin n)
    (inserted fixed : Fin n) (a : ZMod (2 ^ t * q))
    (hfamily : ∀ r,
      PrimitiveOneRetainedCyclePurePresentation g y (set r) leaf r fixed)
    (hleafInj : Function.Injective leaf)
    (hcommonMem : ∀ r, inserted ∈ set r)
    (hleafMem : ∀ r i, leaf i ∈ set r ↔ i ≠ r)
    (hsetsInj : Function.Injective set)
    (hcommonFull :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g inserted - g fixed)) = 2 ^ t)
    (hpow : 4 < 2 ^ t)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    Nonempty
      (PrimitivePuncturedCyclePrivateMatrix
        g y set leaf inserted fixed) := by
  classical
  have hcanonical : ∀ r, ∃ p :
      TwoRetainedCanonicalPrivatePresentation g y (set r),
      p.x = leaf r ∧ p.z = fixed ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) = 2 ^ t ∧
        ∀ i (hi : leaf i ∈ set r), p.weight ⟨leaf i, hi⟩ = -2 := by
    intro r
    exact (hfamily r).exists_canonicalPrivatePresentation
      g y (set r) leaf a r fixed hpow hspan
  choose presentation hpresentation using hcanonical
  exact ⟨{
    state := fun r ↦ (hfamily r).1
    presentation := presentation
    leaf_injective := hleafInj
    common_mem := hcommonMem
    leaf_mem_iff := hleafMem
    missing_first := fun r ↦ (hpresentation r).1
    fixed_second := fun r ↦ (hpresentation r).2.1
    retained_full_order := fun r ↦ (hpresentation r).2.2.1
    common_full_order := hcommonFull
    surviving_weight := fun r ↦ (hpresentation r).2.2.2
    set_injective := hsetsInj }⟩

/-- The common inserted coordinate viewed as an owner in one punctured
transversal. -/
def PrimitivePuncturedCyclePrivateMatrix.commonOwner
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) : ↥(set r) :=
  ⟨inserted, M.common_mem r⟩

/-- The selected scalar of the common inserted owner's private row. -/
def PrimitivePuncturedCyclePrivateMatrix.commonScalar
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) : ℤ :=
  (M.presentation r).scalar (M.commonOwner r)

/-- The selected coefficient vector of the common inserted owner's private
row. -/
def PrimitivePuncturedCyclePrivateMatrix.commonCoeff
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) : Fin n → ℤ :=
  (M.presentation r).coeff (M.commonOwner r)

/-- Every row selected at the common inserted owner retains its nonzero
kernel target, witness equation, nonzero owner diagonal, bounded owner level,
and privacy on the corresponding literal punctured transversal. -/
theorem PrimitivePuncturedCyclePrivateMatrix.common_private_row
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) :
    M.commonScalar r • y ≠ 0 ∧
      Witness g (M.commonScalar r • y) (M.commonCoeff r) ∧
      M.commonCoeff r inserted ≠ 0 ∧
      M.commonCoeff r inserted ∈ twoRetainedExternalCoefficientLevels ∧
      ∀ b ∈ set r, b ≠ inserted → M.commonCoeff r b = 0 := by
  exact ⟨(M.presentation r).target_ne_zero (M.commonOwner r),
    (M.presentation r).isWitness (M.commonOwner r),
    (M.presentation r).owner_ne_zero (M.commonOwner r),
    (M.presentation r).owner_mem (M.commonOwner r),
    (M.presentation r).zero_other (M.commonOwner r)⟩

/-- Every common-owner row has exact three-coordinate support and one of
seven integer profiles.  Writing its coefficients on
`(inserted, missing leaf, fixed)` as `(mu, lambda, gamma)`, the possibilities
are

* `mu = -1`, `-1 ≤ lambda ≤ 2`;
* `mu = 1`, `-1 ≤ lambda ≤ 0`;
* `mu = 2`, `lambda = -1`;

and always `mu + lambda + gamma = 0`. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonCoeff_threeSupport_sevenProfiles
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) :
    (∀ i, i ≠ inserted → i ≠ leaf r → i ≠ fixed →
      M.commonCoeff r i = 0) ∧
    M.commonCoeff r inserted + M.commonCoeff r (leaf r) +
        M.commonCoeff r fixed = 0 ∧
    ((M.commonCoeff r inserted = -1 ∧
        -1 ≤ M.commonCoeff r (leaf r) ∧
        M.commonCoeff r (leaf r) ≤ 2) ∨
      (M.commonCoeff r inserted = 1 ∧
        -1 ≤ M.commonCoeff r (leaf r) ∧
        M.commonCoeff r (leaf r) ≤ 0) ∨
      (M.commonCoeff r inserted = 2 ∧
        M.commonCoeff r (leaf r) = -1)) ∧
    M.commonCoeff r inserted • g inserted +
        M.commonCoeff r (leaf r) • g (leaf r) +
        M.commonCoeff r fixed • g fixed = M.commonScalar r • y := by
  classical
  let c : Fin n → ℤ := M.commonCoeff r
  have hleafNeInserted : leaf r ≠ inserted := by
    intro hli
    have hmem : leaf r ∈ set r := by
      simpa only [hli] using M.common_mem r
    exact ((M.leaf_mem_iff r r).1 hmem) rfl
  have hinsertedNeFixed : inserted ≠ fixed := by
    intro hif
    apply (M.presentation r).z_not_mem
    rw [M.fixed_second r, ← hif]
    exact M.common_mem r
  have hleafNeFixed : leaf r ≠ fixed := by
    intro hlf
    apply (M.presentation r).x_ne_z
    rw [M.missing_first r, M.fixed_second r, hlf]
  have hinsertedNotTail : inserted ∉ ({leaf r, fixed} : Finset (Fin n)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hleafNeInserted, hinsertedNeFixed⟩
  have hleafNotFixed : leaf r ∉ ({fixed} : Finset (Fin n)) := by
    simpa only [Finset.mem_singleton] using hleafNeFixed
  have hzero : ∀ i, i ≠ inserted → i ≠ leaf r → i ≠ fixed → c i = 0 := by
    intro i hiInserted hiLeaf hiFixed
    by_cases hiSet : i ∈ set r
    · exact (M.presentation r).zero_other
        (M.commonOwner r) i hiSet hiInserted
    · have hiComplement : i ∈ Finset.univ \ set r :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hiSet⟩
      rw [(M.presentation r).complement_eq] at hiComplement
      simp only [Finset.mem_insert, Finset.mem_singleton] at hiComplement
      rcases hiComplement with hix | hiz
      · exact False.elim (hiLeaf (hix.trans (M.missing_first r)))
      · exact False.elim (hiFixed (hiz.trans (M.fixed_second r)))
  have hrestrict :
      ∑ i ∈ ({inserted, leaf r, fixed} : Finset (Fin n)), c i =
        ∑ i, c i := by
    exact Finset.sum_subset (by simp) (by
      intro i _ hi
      apply hzero i
      · intro hii
        exact hi (by simp [hii])
      · intro hil
        exact hi (by simp [hil])
      · intro hif
        exact hi (by simp [hif]))
  have hsumRight : c inserted + (c (leaf r) + c fixed) = 0 := by
    calc
      c inserted + (c (leaf r) + c fixed) =
          ∑ i ∈ ({inserted, leaf r, fixed} : Finset (Fin n)), c i := by
            rw [Finset.sum_insert hinsertedNotTail,
              Finset.sum_insert hleafNotFixed]
            simp
      _ = ∑ i, c i := hrestrict
      _ = 0 := (M.presentation r).isWitness (M.commonOwner r) |>.2.2.1
  have hsum : c inserted + c (leaf r) + c fixed = 0 := by
    simpa only [add_assoc] using hsumRight
  have hvalueRestrict :
      ∑ i ∈ ({inserted, leaf r, fixed} : Finset (Fin n)), c i • g i =
        ∑ i, c i • g i := by
    exact Finset.sum_subset (by simp) (by
      intro i _ hi
      rw [hzero i (by
        intro hii
        exact hi (by simp [hii])) (by
        intro hil
        exact hi (by simp [hil])) (by
        intro hif
        exact hi (by simp [hif])), zero_zsmul])
  have hvalueRight : c inserted • g inserted +
      (c (leaf r) • g (leaf r) + c fixed • g fixed) =
        M.commonScalar r • y := by
    calc
      c inserted • g inserted +
          (c (leaf r) • g (leaf r) + c fixed • g fixed) =
          ∑ i ∈ ({inserted, leaf r, fixed} : Finset (Fin n)),
            c i • g i := by
              rw [Finset.sum_insert hinsertedNotTail,
                Finset.sum_insert hleafNotFixed]
              simp
      _ = ∑ i, c i • g i := hvalueRestrict
      _ = M.commonScalar r • y :=
        (M.presentation r).isWitness (M.commonOwner r) |>.2.2.2
  have hvalue : c inserted • g inserted + c (leaf r) • g (leaf r) +
      c fixed • g fixed = M.commonScalar r • y := by
    simpa only [add_assoc] using hvalueRight
  have hownerMem : c inserted ∈ twoRetainedExternalCoefficientLevels := by
    simpa only [c] using (M.common_private_row r).2.2.2.1
  have hmissingLower : -1 ≤ c (leaf r) := by
    simpa only [c,
      PrimitivePuncturedCyclePrivateMatrix.commonCoeff] using
      ((M.presentation r).isWitness (M.commonOwner r)).2.1 (leaf r)
  have hfixedLower : -1 ≤ c fixed := by
    simpa only [c,
      PrimitivePuncturedCyclePrivateMatrix.commonCoeff] using
      ((M.presentation r).isWitness (M.commonOwner r)).2.1 fixed
  have hprofiles :
      (c inserted = -1 ∧ -1 ≤ c (leaf r) ∧ c (leaf r) ≤ 2) ∨
      (c inserted = 1 ∧ -1 ≤ c (leaf r) ∧ c (leaf r) ≤ 0) ∨
      (c inserted = 2 ∧ c (leaf r) = -1) := by
    simp only [twoRetainedExternalCoefficientLevels, Finset.mem_insert,
      Finset.mem_singleton] at hownerMem
    rcases hownerMem with hminus | hone | htwo
    · exact Or.inl ⟨hminus, hmissingLower, by omega⟩
    · exact Or.inr (Or.inl ⟨hone, hmissingLower, by omega⟩)
    · exact Or.inr (Or.inr ⟨htwo, by omega⟩)
  exact ⟨by simpa only [c] using hzero,
    by simpa only [c] using hsum,
    by simpa only [c] using hprofiles,
    by simpa only [c] using hvalue⟩

/-- The seven possible `(common owner, missing leaf)` coefficient pairs.  The
fixed-endpoint coefficient is their negative sum. -/
def puncturedCyclePrivateProfiles : Finset (ℤ × ℤ) :=
  {(-1, -1), (-1, 0), (-1, 1), (-1, 2),
    (1, -1), (1, 0), (2, -1)}

theorem card_puncturedCyclePrivateProfiles :
    puncturedCyclePrivateProfiles.card = 7 := by
  norm_num [puncturedCyclePrivateProfiles]

/-- The finite profile of one common-owner private row. -/
def PrimitivePuncturedCyclePrivateMatrix.commonProfile
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) : ℤ × ℤ :=
  (M.commonCoeff r inserted, M.commonCoeff r (leaf r))

theorem PrimitivePuncturedCyclePrivateMatrix.commonProfile_mem
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) :
    M.commonProfile r ∈ puncturedCyclePrivateProfiles := by
  have hprofile := (M.commonCoeff_threeSupport_sevenProfiles r).2.2.1
  simp only [puncturedCyclePrivateProfiles,
    PrimitivePuncturedCyclePrivateMatrix.commonProfile,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  rcases hprofile with hminus | hone | htwo <;> omega

/-- Seven-profile pigeonhole for the cross-puncture private matrix. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonProfile_capacity_or_largeFiber
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (K : ℕ) :
    d ≤ 7 * K ∨
      ∃ profile ∈ puncturedCyclePrivateProfiles,
        K < (Finset.univ.filter
          (fun r : Fin d ↦ M.commonProfile r = profile)).card := by
  have hcapacity := finiteMap_capacity_or_largeFiber
    puncturedCyclePrivateProfiles M.commonProfile M.commonProfile_mem K
  simpa only [Fintype.card_fin, card_puncturedCyclePrivateProfiles] using
    hcapacity

/-- The actual nonzero odd-kernel target of the common-owner row. -/
def PrimitivePuncturedCyclePrivateMatrix.commonTarget
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) : ZMod (2 ^ t * q) :=
  M.commonScalar r • y

/-- Two elements of the same positive power-of-two order cannot be related by
doubling. -/
theorem ne_two_nsmul_of_addOrderOf_eq_same_twoPower
    {Q : Type*} [AddCommGroup Q] [Finite Q]
    {t : ℕ} (ht : 1 ≤ t) (delta beta : Q)
    (hdelta : addOrderOf delta = 2 ^ t)
    (hbeta : addOrderOf beta = 2 ^ t) :
    delta ≠ (2 : ℕ) • beta := by
  intro heq
  have hpowEq : 2 ^ (t - 1) * 2 = 2 ^ t := by
    calc
      2 ^ (t - 1) * 2 = 2 ^ ((t - 1) + 1) := (pow_succ 2 (t - 1)).symm
      _ = 2 ^ t := by congr 1; omega
  have hzero : (2 ^ (t - 1)) • delta = 0 := by
    rw [heq, ← mul_nsmul beta 2 (2 ^ (t - 1)), Nat.mul_comm, hpowEq]
    simpa only [hbeta] using addOrderOf_nsmul_eq_zero beta
  have hdvd : 2 ^ t ∣ 2 ^ (t - 1) := by
    rw [← hdelta]
    exact addOrderOf_dvd_of_nsmul_eq_zero hzero
  have hle : 2 ^ t ≤ 2 ^ (t - 1) :=
    Nat.le_of_dvd (by positivity) hdvd
  have hlt : 2 ^ (t - 1) < 2 ^ t :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  omega

/-- The raw three-supported witness gives a two-generator relation in the
quotient: `mu * delta + lambda * beta = 0`. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonProfile_quotientRelation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (r : Fin d) :
    M.commonCoeff r inserted •
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g inserted - g fixed) +
      M.commonCoeff r (leaf r) •
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (leaf r) - g fixed) = 0 := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  have hsum := (M.commonCoeff_threeSupport_sevenProfiles r).2.1
  have hvalue := (M.commonCoeff_threeSupport_sevenProfiles r).2.2.2
  have hfixedCoeff :
      M.commonCoeff r fixed =
        -(M.commonCoeff r inserted + M.commonCoeff r (leaf r)) := by
    omega
  have htargetMem : M.commonTarget r ∈ H := by
    exact AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples y) _
  have hmem :
      M.commonCoeff r inserted • (g inserted - g fixed) +
        M.commonCoeff r (leaf r) • (g (leaf r) - g fixed) ∈ H := by
    change M.commonScalar r • y ∈ H at htargetMem
    rw [← hvalue] at htargetMem
    rw [hfixedCoeff] at htargetMem
    convert htargetMem using 1
    module
  apply (QuotientAddGroup.eq_zero_iff
    (M.commonCoeff r inserted • (g inserted - g fixed) +
      M.commonCoeff r (leaf r) • (g (leaf r) - g fixed))).2
  exact hmem

/-- Only three of the seven sparse profiles are compatible with full order
for both the common inserted difference and the missing-leaf difference. -/
def puncturedCycleFullOrderPrivateProfiles : Finset (ℤ × ℤ) :=
  {(-1, -1), (-1, 1), (1, -1)}

theorem card_puncturedCycleFullOrderPrivateProfiles :
    puncturedCycleFullOrderPrivateProfiles.card = 3 := by
  norm_num [puncturedCycleFullOrderPrivateProfiles]

theorem PrimitivePuncturedCyclePrivateMatrix.commonProfile_mem_fullOrderProfiles
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (ht : 1 ≤ t) (r : Fin d) :
    M.commonProfile r ∈ puncturedCycleFullOrderPrivateProfiles := by
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g inserted - g fixed)
  let betaQ : Q := pi (g (leaf r) - g fixed)
  have hdelta : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, pi, H, Q] using M.common_full_order
  have hbeta : addOrderOf betaQ = 2 ^ t := by
    have horder := M.retained_full_order r
    simpa only [deltaQ, betaQ, pi, H, Q, M.missing_first r,
      M.fixed_second r] using horder
  have hrelation : M.commonCoeff r inserted • deltaQ +
      M.commonCoeff r (leaf r) • betaQ = 0 := by
    simpa only [deltaQ, betaQ, pi, H, Q] using
      M.commonProfile_quotientRelation r
  have hprofile := M.commonProfile_mem r
  simp only [puncturedCyclePrivateProfiles,
    PrimitivePuncturedCyclePrivateMatrix.commonProfile,
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq] at hprofile
  rcases hprofile with h₁ | h₂ | h₃ | h₄ | h₅ | h₆ | h₇
  · simp only [puncturedCycleFullOrderPrivateProfiles,
      PrimitivePuncturedCyclePrivateMatrix.commonProfile,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    exact Or.inl h₁
  · have hzero : deltaQ = 0 := by
      rw [h₂.1, h₂.2] at hrelation
      simpa only [neg_one_zsmul, zero_zsmul, add_zero, neg_eq_zero] using
        hrelation
    rw [hzero] at hdelta
    norm_num at hdelta
    have : 1 < 2 ^ t := one_lt_pow₀ (by omega) (by omega)
    omega
  · simp only [puncturedCycleFullOrderPrivateProfiles,
      PrimitivePuncturedCyclePrivateMatrix.commonProfile,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    exact Or.inr (Or.inl h₃)
  · have heq : deltaQ = (2 : ℕ) • betaQ := by
      rw [h₄.1, h₄.2] at hrelation
      have hsub : (2 : ℤ) • betaQ - deltaQ = 0 := by
        simpa only [neg_one_zsmul, sub_eq_add_neg, add_comm] using hrelation
      have heqZ : deltaQ = (2 : ℤ) • betaQ :=
        (sub_eq_zero.mp hsub).symm
      simpa only [two_nsmul, two_zsmul] using heqZ
    exact (ne_two_nsmul_of_addOrderOf_eq_same_twoPower
      ht deltaQ betaQ hdelta hbeta heq).elim
  · simp only [puncturedCycleFullOrderPrivateProfiles,
      PrimitivePuncturedCyclePrivateMatrix.commonProfile,
      Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
    exact Or.inr (Or.inr h₅)
  · have hzero : deltaQ = 0 := by
      rw [h₆.1, h₆.2] at hrelation
      simpa only [one_zsmul, zero_zsmul, add_zero] using hrelation
    rw [hzero] at hdelta
    norm_num at hdelta
    have : 1 < 2 ^ t := one_lt_pow₀ (by omega) (by omega)
    omega
  · have heq : betaQ = (2 : ℕ) • deltaQ := by
      rw [h₇.1, h₇.2] at hrelation
      have hsub : (2 : ℤ) • deltaQ - betaQ = 0 := by
        simpa only [neg_one_zsmul, sub_eq_add_neg] using hrelation
      have heqZ : betaQ = (2 : ℤ) • deltaQ :=
        (sub_eq_zero.mp hsub).symm
      simpa only [two_nsmul, two_zsmul] using heqZ
    exact (ne_two_nsmul_of_addOrderOf_eq_same_twoPower
      ht betaQ deltaQ hbeta hdelta heq).elim

/-- Rows in one exact profile differ only through their missing-leaf term. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonTarget_sub_eq_zsmul_leaf_sub_of_profile_eq
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) {r s : Fin d}
    (hprofile : M.commonProfile r = M.commonProfile s) :
    M.commonTarget s - M.commonTarget r =
      M.commonCoeff r (leaf r) • (g (leaf s) - g (leaf r)) := by
  have hmu : M.commonCoeff r inserted = M.commonCoeff s inserted := by
    exact congrArg Prod.fst hprofile
  have hlambda :
      M.commonCoeff r (leaf r) = M.commonCoeff s (leaf s) := by
    exact congrArg Prod.snd hprofile
  have hsumR := (M.commonCoeff_threeSupport_sevenProfiles r).2.1
  have hsumS := (M.commonCoeff_threeSupport_sevenProfiles s).2.1
  have hfixed : M.commonCoeff r fixed = M.commonCoeff s fixed := by
    omega
  have hvalueR := (M.commonCoeff_threeSupport_sevenProfiles r).2.2.2
  have hvalueS := (M.commonCoeff_threeSupport_sevenProfiles s).2.2.2
  calc
    M.commonTarget s - M.commonTarget r =
        (M.commonCoeff s inserted • g inserted +
          M.commonCoeff s (leaf s) • g (leaf s) +
          M.commonCoeff s fixed • g fixed) -
        (M.commonCoeff r inserted • g inserted +
          M.commonCoeff r (leaf r) • g (leaf r) +
          M.commonCoeff r fixed • g fixed) := by
            rw [hvalueS, hvalueR]
            rfl
    _ = M.commonCoeff r (leaf r) •
        (g (leaf s) - g (leaf r)) := by
      rw [← hmu, ← hlambda, ← hfixed]
      module

/-- On an edge that stays inside one profile, the private target difference
is the missing-leaf coefficient times the original doubling displacement. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonTarget_cycleEdge_sub_eq
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ t * q))
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (r : Fin d) (hprofile : M.commonProfile (R r) = M.commonProfile r) :
    M.commonTarget (R r) - M.commonTarget r =
      M.commonCoeff r (leaf r) • (g (leaf r) - a) := by
  have htarget :=
    M.commonTarget_sub_eq_zsmul_leaf_sub_of_profile_eq hprofile.symm
  have hleafDiff : g (leaf (R r)) - g (leaf r) = g (leaf r) - a := by
    have hr := hdouble r
    calc
      g (leaf (R r)) - g (leaf r) =
          (g (leaf (R r)) - a) - (g (leaf r) - a) := by abel
      _ = (2 : ℤ) • (g (leaf r) - a) - (g (leaf r) - a) := by
        rw [hr]
      _ = g (leaf r) - a := by module
  rw [hleafDiff] at htarget
  exact htarget

/-- Either of the two zero-missing-coefficient profiles occurs at most once.
Indeed its exact three-supported coefficient vector is determined entirely by
the profile, so HY's cross-puncture injectivity identifies the punctures. -/
theorem PrimitivePuncturedCyclePrivateMatrix.eq_of_commonProfile_eq_of_missingCoeff_eq_zero
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed)
    (hcoeffInjective : Function.Injective M.commonCoeff)
    {r s : Fin d} (hmissing : M.commonCoeff r (leaf r) = 0)
    (hprofile : M.commonProfile r = M.commonProfile s) : r = s := by
  apply hcoeffInjective
  have hmu : M.commonCoeff r inserted = M.commonCoeff s inserted :=
    congrArg Prod.fst hprofile
  have hlambda :
      M.commonCoeff r (leaf r) = M.commonCoeff s (leaf s) :=
    congrArg Prod.snd hprofile
  have hmissingS : M.commonCoeff s (leaf s) = 0 := by
    rw [← hlambda, hmissing]
  have hsumR := (M.commonCoeff_threeSupport_sevenProfiles r).2.1
  have hsumS := (M.commonCoeff_threeSupport_sevenProfiles s).2.1
  have hfixed : M.commonCoeff r fixed = M.commonCoeff s fixed := by omega
  have hsupportR := (M.commonCoeff_threeSupport_sevenProfiles r).1
  have hsupportS := (M.commonCoeff_threeSupport_sevenProfiles s).1
  funext i
  by_cases hiInserted : i = inserted
  · subst i
    exact hmu
  by_cases hiFixed : i = fixed
  · subst i
    exact hfixed
  have hzeroR : M.commonCoeff r i = 0 := by
    by_cases hiLeaf : i = leaf r
    · subst i
      exact hmissing
    · exact hsupportR i hiInserted hiLeaf hiFixed
  have hzeroS : M.commonCoeff s i = 0 := by
    by_cases hiLeaf : i = leaf s
    · subst i
      exact hmissingS
    · exact hsupportS i hiInserted hiLeaf hiFixed
  rw [hzeroR, hzeroS]

theorem PrimitivePuncturedCyclePrivateMatrix.zeroMissing_profileFiber_card_le_one
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed)
    (hcoeffInjective : Function.Injective M.commonCoeff)
    (profile : ℤ × ℤ) (hzero : profile.2 = 0) :
    (Finset.univ.filter
      (fun r : Fin d ↦ M.commonProfile r = profile)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro r hr s hs
  have hrProfile := (Finset.mem_filter.mp hr).2
  have hsProfile := (Finset.mem_filter.mp hs).2
  have hrMissing : M.commonCoeff r (leaf r) = 0 := by
    calc
      M.commonCoeff r (leaf r) = (M.commonProfile r).2 := rfl
      _ = profile.2 := congrArg Prod.snd hrProfile
      _ = 0 := hzero
  exact M.eq_of_commonProfile_eq_of_missingCoeff_eq_zero hcoeffInjective
    hrMissing (hrProfile.trans hsProfile.symm)

/-- Private coefficient rows attached to distinct punctures are distinct.
If two rows agreed, privacy in the other puncture would make the missing-leaf
coefficient zero.  The normalized row would then kill twice the common
inserted-to-fixed difference, contradicting its full `2^t` quotient order. -/
theorem PrimitivePuncturedCyclePrivateMatrix.commonCoeff_injective
    {t q : ℕ} [NeZero (2 ^ t * q)]
    {g : Fin n → ZMod (2 ^ t * q)} {y : ZMod (2 ^ t * q)}
    {d : ℕ} {set : Fin d → Finset (Fin n)} {leaf : Fin d → Fin n}
    {inserted fixed : Fin n}
    (M : PrimitivePuncturedCyclePrivateMatrix
      g y set leaf inserted fixed) (hpow : 2 < 2 ^ t) :
    Function.Injective M.commonCoeff := by
  intro r s hrs
  by_contra hrsNe
  have hrMemS : leaf r ∈ set s :=
    (M.leaf_mem_iff s r).2 hrsNe
  have hrNeInserted : leaf r ≠ inserted := by
    intro hri
    have : leaf r ∈ set r := by simpa only [hri] using M.common_mem r
    exact ((M.leaf_mem_iff r r).1 this) rfl
  have hzeroS : M.commonCoeff s (leaf r) = 0 :=
    (M.presentation s).zero_other (M.commonOwner s)
      (leaf r) hrMemS hrNeInserted
  have hzeroR : M.commonCoeff r (leaf r) = 0 := by
    rw [hrs]
    exact hzeroS
  have hweightR :
      (M.presentation r).weight (M.commonOwner r) = 0 := by
    rw [(M.presentation r).weight_eq, M.missing_first r]
    change twoRetainedOwnerNormalization
      (M.commonCoeff r inserted) * M.commonCoeff r (leaf r) = 0
    rw [hzeroR, mul_zero]
  let pFive :=
    (M.presentation r).toFiveWeightPresentation g y (set r)
  have hrow := pFive.row_mem (M.commonOwner r)
  have hmem :
      (2 : ℤ) • (g inserted - g fixed) ∈ AddSubgroup.zmultiples y := by
    change (2 : ℤ) • (g inserted - g (M.presentation r).z) +
      (M.presentation r).weight (M.commonOwner r) •
        (g (M.presentation r).x - g (M.presentation r).z) ∈
          AddSubgroup.zmultiples y at hrow
    rw [M.fixed_second r, hweightR, zero_zsmul, add_zero] at hrow
    exact hrow
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let deltaQ : Q := pi (g inserted - g fixed)
  have hzeroZ : (2 : ℤ) • deltaQ = 0 := by
    rw [← map_zsmul]
    exact (QuotientAddGroup.eq_zero_iff
      ((2 : ℤ) • (g inserted - g fixed))).2 hmem
  have hzeroN : (2 : ℕ) • deltaQ = 0 := by
    simpa only [two_nsmul, two_zsmul] using hzeroZ
  have horder : addOrderOf deltaQ = 2 ^ t := by
    simpa only [deltaQ, pi, H, Q] using M.common_full_order
  have hdvd : 2 ^ t ∣ 2 := by
    rw [← horder]
    exact addOrderOf_dvd_of_nsmul_eq_zero hzeroN
  have hle : 2 ^ t ≤ 2 := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The constant cycle and the exact quotient-row normal form use one and the
same presentation.  In particular, no orientation or existential witness is
lost before the positive-stratum descent step. -/
theorem PrimitiveTwoRetainedPositiveStratumRows.fullDeletedCycle_exactPresentation
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedPositiveStratumRows g y B)
    (hpow : 18 < 2 ^ t)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ t * q))
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ p : TwoRetainedFiveWeightPresentation g y B,
      PrimitiveTwoRetainedPositiveStratumPresentation g y B p ∧
      ∀ i j,
        p.weight ⟨leaf i, hleafB i⟩ =
          p.weight ⟨leaf j, hleafB j⟩ := by
  rcases hstate with ⟨hmin, hretained, hrows, p, hpfull⟩
  refine ⟨p, ⟨hmin, hretained, hrows, hpfull⟩, ?_⟩
  exact p.fullDeleted_weight_constant_of_fullOrder
    g y B hpfull.1 hpow hd leaf R a hleafB hdouble

/-- In a full-order positive-stratum state, a fully deleted doubling cycle
has constant five-weight label as soon as the quotient order exceeds the
universal coefficient bound `18` from `fullDeletedCycle_split`. -/
theorem PrimitiveTwoRetainedPositiveStratumRows.fullDeletedCycle_weight_constant_of_eighteen_lt_twoPower
    {t q : ℕ} [NeZero (2 ^ t * q)]
    (g : Fin n → ZMod (2 ^ t * q)) (y : ZMod (2 ^ t * q))
    (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedPositiveStratumRows g y B)
    (hpow : 18 < 2 ^ t)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ t * q))
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ∀ i j,
        weight ⟨leaf i, hleafB i⟩ = weight ⟨leaf j, hleafB j⟩ := by
  classical
  rcases hstate with ⟨_hmin, _hretained, hrows, p, hpfull⟩
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  have hpOrder : addOrderOf (pi (g p.x - g p.z)) = 2 ^ t := by
    simpa only [pi, H, Q] using hpfull.1
  obtain ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight,
      hsmall | hconstant⟩ :=
    hrows.fullDeletedCycle_split g y B hd leaf R a hleafB hdouble
  · have hxCase : x = p.x ∨ x = p.z := by
      have hxMem : x ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hxB⟩
      rw [p.complement_eq] at hxMem
      simpa using hxMem
    have hzCase : z = p.x ∨ z = p.z := by
      have hzMem : z ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hzB⟩
      rw [p.complement_eq] at hzMem
      simpa using hzMem
    have hxzOrder : addOrderOf (pi (g x - g z)) = 2 ^ t := by
      rcases hxCase with hxpX | hxpZ
      · have hzpZ : z = p.z := hzCase.resolve_left (by
          intro hzpX
          exact hxz (hxpX.trans hzpX.symm))
        simpa only [hxpX, hzpZ] using hpOrder
      · have hzpX : z = p.x := hzCase.resolve_right (by
          intro hzpZ
          exact hxz (hxpZ.trans hzpZ.symm))
        have hneg : g x - g z = -(g p.x - g p.z) := by
          rw [hxpZ, hzpX]
          abel
        rw [hneg, map_neg, addOrderOf_neg]
        exact hpOrder
    obtain ⟨e, he, helow, hehigh, heMem⟩ := hsmall
    have heQuotient : e • pi (g x - g z) = 0 := by
      rw [← map_zsmul]
      exact (QuotientAddGroup.eq_zero_iff (e • (g x - g z))).2 heMem
    have hnatQuotient : e.natAbs • pi (g x - g z) = 0 := by
      rw [← natCast_zsmul]
      rcases Int.natAbs_eq e with hePos | heNeg
      · rw [hePos] at heQuotient
        exact heQuotient
      · rw [heNeg, neg_smul] at heQuotient
        exact neg_eq_zero.mp heQuotient
    have horderDvd : 2 ^ t ∣ e.natAbs := by
      rw [← hxzOrder]
      exact addOrderOf_dvd_of_nsmul_eq_zero hnatQuotient
    have horderLe : 2 ^ t ≤ e.natAbs :=
      Nat.le_of_dvd (Int.natAbs_pos.mpr he) horderDvd
    have habsLe : e.natAbs ≤ 18 := by
      rcases Int.natAbs_eq e with hePos | heNeg
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
      · have : (e.natAbs : ℤ) ≤ 18 := by omega
        exact_mod_cast this
    omega
  · exact ⟨x, z, weight, hxB, hzB, hxz, hcomplement, hweight, hconstant⟩

/-- Fifth-stratum specialization of full-order fully-deleted-cycle
constancy. -/
theorem PrimitiveTwoRetainedPositiveStratumRows.fullDeletedCycle_weight_constant_of_fifthStratum
    {q : ℕ} [NeZero (2 ^ 5 * q)]
    (g : Fin n → ZMod (2 ^ 5 * q)) (y : ZMod (2 ^ 5 * q))
    (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedPositiveStratumRows g y B)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (R : Equiv.Perm (Fin d)) (a : ZMod (2 ^ 5 * q))
    (hleafB : ∀ i, leaf i ∈ B)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a)) :
    ∃ x z : Fin n, ∃ weight : ↥B → ℤ,
      x ∉ B ∧ z ∉ B ∧ x ≠ z ∧ Finset.univ \ B = {x, z} ∧
      (∀ b, weight b ∈ twoRetainedNormalizedWeightLevels) ∧
      ∀ i j,
        weight ⟨leaf i, hleafB i⟩ = weight ⟨leaf j, hleafB j⟩ := by
  exact hstate.fullDeletedCycle_weight_constant_of_eighteen_lt_twoPower
    g y B (by norm_num) hd leaf R a hleafB hdouble

/-- Minimize one literal positive-stratum primitive-owner exchange.  A strict
shrink enters C2; equality retains the literal exchanged deletion set as a
full-order two-retained state. -/
theorem exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    {B : Finset (Fin n)}
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hretained : n - B.card = 2)
    {b x z : Fin n} (hb : b ∈ B) (hxB : x ∉ B) (hzB : z ∉ B)
    (hxz : x ≠ z) (hcomplement : Finset.univ \ B = {x, z})
    (hprimitive :
      let H := AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
        QuotientAddGroup.mk' H
      addOrderOf (pi (g b - g z)) = 2 ^ t)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      PrimitiveTwoRetainedPositiveStratumRows g y
        (insert x (B.erase b)) := by
  classical
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let pi : ZMod (2 ^ t * q) →+ ZMod (2 ^ t * q) ⧸ H :=
    QuotientAddGroup.mk' H
  have htwo : 2 ≤ 2 ^ t := by
    simpa using Nat.pow_le_pow_right (by omega : 0 < (2 : ℕ)) ht
  have hquotientNe : pi (g b - g z) ≠ 0 := by
    intro hzero
    have horder : addOrderOf (pi (g b - g z)) = 2 ^ t := by
      simpa only [pi, H] using hprimitive
    rw [hzero] at horder
    norm_num at horder
    omega
  have hdiff : g b - g z ∉ AddSubgroup.zmultiples y := by
    intro hmem
    exact hquotientNe ((QuotientAddGroup.eq_zero_iff (g b - g z)).2 hmem)
  let Bexchange : Finset (Fin n) := insert x (B.erase b)
  have hBexchange : CyclicKernelSupportTransversal g y Bexchange := by
    simpa only [Bexchange] using
      cyclicKernelSupportTransversal_exchange_of_pairDifference_not_mem
        g y hmin.1 hb hxB hzB hxz hcomplement hdiff
  obtain ⟨B₀, hB₀sub, hB₀min⟩ :=
    exists_minimalCyclicKernelSupportTransversal_subset g y hBexchange
  have hBexchangeCard : Bexchange.card = B.card := by
    simpa only [Bexchange] using card_erase_insert_retained_eq hb hxB
  have hB₀card : B₀.card ≤ B.card := by
    calc
      B₀.card ≤ Bexchange.card := Finset.card_le_card hB₀sub
      _ = B.card := hBexchangeCard
  by_cases hstrict : B₀.card < B.card
  · left
    refine ⟨B₀, hB₀min, ?_⟩
    have hBcard : B.card ≤ n := by
      simpa using Finset.card_le_univ B
    omega
  · right
    have hcardEq : B₀.card = B.card := by omega
    have hB₀eq : B₀ = Bexchange := by
      apply Finset.eq_of_subset_of_card_le hB₀sub
      rw [hBexchangeCard, hcardEq]
    have hretained₀ : n - B₀.card = 2 := by omega
    have hrows₀ := twoRetainedMinimalCyclicKernelPrivateRows_of_minimalTransversal
      g hg hh hne hunique hno y hB₀min hretained₀
    have hfive₀ := hrows₀.fiveWeightRows g y B₀
    obtain ⟨p₀⟩ := hfive₀.fiveWeightPresentation g y B₀
    have hcomplement₀ : Finset.univ \ B₀ = {b, z} := by
      rw [hB₀eq]
      simpa only [Bexchange] using
        complement_erase_insert_retained hb hxB hzB hxz hcomplement
    have hp₀x : p₀.x = b ∨ p₀.x = z := by
      have hxMem : p₀.x ∈ Finset.univ \ B₀ :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, p₀.x_not_mem⟩
      rw [hcomplement₀] at hxMem
      simpa using hxMem
    have hp₀z : p₀.z = b ∨ p₀.z = z := by
      have hzMem : p₀.z ∈ Finset.univ \ B₀ :=
        Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, p₀.z_not_mem⟩
      rw [hcomplement₀] at hzMem
      simpa using hzMem
    have hp₀primitive : addOrderOf (pi (g p₀.x - g p₀.z)) = 2 ^ t := by
      rcases hp₀x with hxb | hxz'
      · have hzz : p₀.z = z := hp₀z.resolve_left (by
          intro hzb
          exact p₀.x_ne_z (hxb.trans hzb.symm))
        simpa only [hxb, hzz, pi, H] using hprimitive
      · have hzb : p₀.z = b := hp₀z.resolve_right (by
          intro hzz
          exact p₀.x_ne_z (hxz'.trans hzz.symm))
        have hneg : g p₀.x - g p₀.z = -(g b - g z) := by
          rw [hxz', hzb]
          abel
        rw [hneg, map_neg, addOrderOf_neg]
        simpa only [pi, H] using hprimitive
    have hnormal := p₀.positiveStratum_completeQuotientRowNormalForm_withExchangeSeed
      ht g hg hunique hne y hyq hfullOdd B₀ hfive₀ hminimal
    have hhalfLt : 2 ^ (t - 1) < 2 ^ t :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    have hsolved :
        ∀ b₀ : ↥B₀, ∃ k : ℤ, p₀.weight b₀ = 2 * k ∧
          (pi (g (b₀ : Fin n) - g p₀.z) =
              -(k • pi (g p₀.x - g p₀.z)) ∨
            pi (g (b₀ : Fin n) - g p₀.z) =
              (2 ^ (t - 1) : ℕ) • pi (g p₀.x - g p₀.z) -
                k • pi (g p₀.x - g p₀.z)) := by
      rcases hnormal with hfirst | hhalf | hfull
      · have hpowOne : 2 ^ t = 1 := by
          exact hp₀primitive.symm.trans hfirst.2.1
        omega
      · have hpowHalf : 2 ^ t = 2 ^ (t - 1) := by
          exact hp₀primitive.symm.trans hhalf.1
        omega
      · simpa only [pi, H] using hfull.2
    have hstate₀ : PrimitiveTwoRetainedPositiveStratumRows g y B₀ := by
      refine ⟨hB₀min, hretained₀, hfive₀, p₀, ?_⟩
      simpa only [pi, H] using And.intro hp₀primitive hsolved
    rw [hB₀eq] at hstate₀
    simpa only [Bexchange] using hstate₀

/-- Exchange any named deleted owner in an explicit full-order presentation.
One of the two retained orientations is primitive, so minimization either
enters C2 or preserves one of the two literal exchanged deletion sets as a
new full-order exact-two state. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_owner_to_fullOrder_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    (b : ↥B) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      PrimitiveTwoRetainedPositiveStratumRows g y
          (insert p.x (B.erase (b : Fin n))) ∨
        PrimitiveTwoRetainedPositiveStratumRows g y
          (insert p.z (B.erase (b : Fin n))) := by
  classical
  have horientation := hpres.owner_primitive_at_one_retained g y B p b
  rcases hpres with ⟨hmin, hretained, hrows, _hfull⟩
  rcases horientation with hprimitiveZ | hprimitiveX
  · rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
        ht g hg hh hne hunique hno y hyq hfullOdd hmin hretained b.property
          p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq hprimitiveZ
            hminimal with
      hthree | hexact
    · exact Or.inl hthree
    · exact Or.inr (Or.inl hexact)
  · have hcomplementReverse : Finset.univ \ B = {p.z, p.x} := by
      simpa only [pair_comm] using p.complement_eq
    rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
        ht g hg hh hne hunique hno y hyq hfullOdd hmin hretained b.property
          p.z_not_mem p.x_not_mem p.x_ne_z.symm hcomplementReverse
            hprimitiveX hminimal with
      hthree | hexact
    · exact Or.inl hthree
    · exact Or.inr (Or.inr hexact)

/-- On a fully deleted cycle, exchanging any chosen leaf either enters C2 or
produces a literal one-retained-leaf cycle state.  This is the uniform
full-to-punctured transition needed for the remaining positive-stratum
descent. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_fullDeleted_cycleLeaf_to_oneRetained_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (hleafB : ∀ i, leaf i ∈ B) (r : Fin d) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      (PrimitiveTwoRetainedPositiveStratumRows g y
          (insert p.x (B.erase (leaf r))) ∧
        ∀ i, leaf i ∈ insert p.x (B.erase (leaf r)) ↔ i ≠ r) ∨
      (PrimitiveTwoRetainedPositiveStratumRows g y
          (insert p.z (B.erase (leaf r))) ∧
        ∀ i, leaf i ∈ insert p.z (B.erase (leaf r)) ↔ i ≠ r) := by
  classical
  have hrB : leaf r ∈ B := hleafB r
  let b : ↥B := ⟨leaf r, hrB⟩
  have hxOutside : p.x ∉ Set.range leaf := by
    rintro ⟨i, hix⟩
    apply p.x_not_mem
    rw [← hix]
    exact hleafB i
  have hzOutside : p.z ∉ Set.range leaf := by
    rintro ⟨i, hiz⟩
    apply p.z_not_mem
    rw [← hiz]
    exact hleafB i
  rcases hpres.exchange_owner_to_fullOrder_or_three
      ht g hg hh hne hunique hno y hyq hfullOdd B p hminimal b with
    hthree | hx | hz
  · exact Or.inl hthree
  · exact Or.inr (Or.inl ⟨by simpa only [b] using hx,
      cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hxOutside⟩)
  · exact Or.inr (Or.inr ⟨by simpa only [b] using hz,
      cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hzOutside⟩)

/-- The odd-kernel cycle coset makes the primitive exchange orientation
uniform over all fully deleted leaves.  Therefore either one leaf exchange
enters C2, or every leaf simultaneously supplies a literal full-order
exact-two transversal using the same retained endpoint. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_all_fullDeleted_cycleLeaves_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (hleafInj : Function.Injective leaf)
    (a : ZMod (2 ^ t * q)) (hleafB : ∀ i, leaf i ∈ B)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ((∀ r,
          PrimitiveTwoRetainedPositiveStratumRows g y
            (insert p.x (B.erase (leaf r)))) ∧
        Function.Injective
          (fun r ↦ insert p.x (B.erase (leaf r)))) ∨
      ((∀ r,
          PrimitiveTwoRetainedPositiveStratumRows g y
            (insert p.z (B.erase (leaf r)))) ∧
        Function.Injective
          (fun r ↦ insert p.z (B.erase (leaf r)))) := by
  classical
  let H : AddSubgroup (ZMod (2 ^ t * q)) := AddSubgroup.zmultiples y
  let Q := ZMod (2 ^ t * q) ⧸ H
  let pi : ZMod (2 ^ t * q) →+ Q := QuotientAddGroup.mk' H
  let r₀ : Fin d := ⟨0, hd⟩
  have hcosetZ : ∀ r,
      pi (g (leaf r) - g p.z) = pi (g (leaf r₀) - g p.z) := by
    intro r
    exact cycle_quotient_displacement_eq_of_span
      g y a (g p.z) leaf hspan r r₀
  have hcosetX : ∀ r,
      pi (g (leaf r) - g p.x) = pi (g (leaf r₀) - g p.x) := by
    intro r
    exact cycle_quotient_displacement_eq_of_span
      g y a (g p.x) leaf hspan r r₀
  let b₀ : ↥B := ⟨leaf r₀, hleafB r₀⟩
  have horientation := hpres.owner_primitive_at_one_retained g y B p b₀
  rcases hpres with ⟨hmin, hretained, _hrows, _hfull⟩
  rcases horientation with hprimitiveZ | hprimitiveX
  · by_cases hthree : ∃ r : Fin d, ∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card
    · obtain ⟨_r, B₀, hB₀⟩ := hthree
      exact Or.inl ⟨B₀, hB₀⟩
    · right
      left
      refine ⟨?_, insert_erase_cycleLeaf_injective
        leaf hleafInj hleafB p.x_not_mem⟩
      intro r
      have hprimitiveZr :
          addOrderOf (pi (g (leaf r) - g p.z)) = 2 ^ t := by
        rw [hcosetZ r]
        simpa only [b₀, pi, H, Q] using hprimitiveZ
      let br : ↥B := ⟨leaf r, hleafB r⟩
      rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
          ht g hg hh hne hunique hno y hyq hfullOdd hmin hretained
            br.property p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
              hprimitiveZr hminimal with
        hthreeR | hexact
      · exfalso
        apply hthree
        exact ⟨r, hthreeR⟩
      · simpa only [br] using hexact
  · by_cases hthree : ∃ r : Fin d, ∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card
    · obtain ⟨_r, B₀, hB₀⟩ := hthree
      exact Or.inl ⟨B₀, hB₀⟩
    · right
      right
      refine ⟨?_, insert_erase_cycleLeaf_injective
        leaf hleafInj hleafB p.z_not_mem⟩
      intro r
      have hprimitiveXr :
          addOrderOf (pi (g (leaf r) - g p.x)) = 2 ^ t := by
        rw [hcosetX r]
        simpa only [b₀, pi, H, Q] using hprimitiveX
      have hcomplementReverse : Finset.univ \ B = {p.z, p.x} := by
        simpa only [pair_comm] using p.complement_eq
      let br : ↥B := ⟨leaf r, hleafB r⟩
      rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
          ht g hg hh hne hunique hno y hyq hfullOdd hmin hretained
            br.property p.z_not_mem p.x_not_mem p.x_ne_z.symm
              hcomplementReverse hprimitiveXr hminimal with
        hthreeR | hexact
      · exfalso
        apply hthree
        exact ⟨r, hthreeR⟩
      · simpa only [br] using hexact

/-- Simultaneous cycle exchange in a directly comparable row normal form.
Unless C2 is reached, every missing leaf has a distinct punctured transversal
whose retained pair is oriented as `(missing leaf, fixed endpoint)` and whose
surviving cycle rows all have weight `-2`. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_all_fullDeleted_cycleLeaves_to_purePresentations_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (hleafInj : Function.Injective leaf)
    (a : ZMod (2 ^ t * q)) (hleafB : ∀ i, leaf i ∈ B)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (hpow : 4 < 2 ^ t) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ((∀ r,
          PrimitiveOneRetainedCyclePurePresentation g y
            (insert p.x (B.erase (leaf r))) leaf r p.z) ∧
        Function.Injective
          (fun r ↦ insert p.x (B.erase (leaf r)))) ∨
      ((∀ r,
          PrimitiveOneRetainedCyclePurePresentation g y
            (insert p.z (B.erase (leaf r))) leaf r p.x) ∧
        Function.Injective
          (fun r ↦ insert p.z (B.erase (leaf r)))) := by
  classical
  have hxOutside : p.x ∉ Set.range leaf := by
    rintro ⟨i, hix⟩
    apply p.x_not_mem
    rw [← hix]
    exact hleafB i
  have hzOutside : p.z ∉ Set.range leaf := by
    rintro ⟨i, hiz⟩
    apply p.z_not_mem
    rw [← hiz]
    exact hleafB i
  rcases hpres.exchange_all_fullDeleted_cycleLeaves_or_three
      ht g hg hh hne hunique hno y hyq hfullOdd B p hminimal hd leaf
        hleafInj a hleafB hspan with
    hthree | hx | hz
  · exact Or.inl hthree
  · right
    left
    refine ⟨?_, hx.2⟩
    intro r
    let Br : Finset (Fin n) := insert p.x (B.erase (leaf r))
    have hincidence : ∀ i, leaf i ∈ Br ↔ i ≠ r := by
      simpa only [Br] using cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hxOutside
    have hzBr : p.z ∉ Br := by
      simp only [Br, Finset.mem_insert, Finset.mem_erase, Ne.symm p.x_ne_z,
        false_or, p.z_not_mem, and_false, not_false_eq_true]
    have hrz : leaf r ≠ p.z := by
      intro hrz
      apply p.z_not_mem
      rw [← hrz]
      exact hleafB r
    apply PrimitiveTwoRetainedPositiveStratumRows.to_oneRetainedCyclePurePresentation
      g y Br (by simpa only [Br] using hx.1 r) hpow leaf a r hincidence
        hspan p.z hzBr hrz
  · right
    right
    refine ⟨?_, hz.2⟩
    intro r
    let Br : Finset (Fin n) := insert p.z (B.erase (leaf r))
    have hincidence : ∀ i, leaf i ∈ Br ↔ i ≠ r := by
      simpa only [Br] using cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hzOutside
    have hxBr : p.x ∉ Br := by
      simp only [Br, Finset.mem_insert, Finset.mem_erase, p.x_ne_z,
        false_or, p.x_not_mem, and_false, not_false_eq_true]
    have hrx : leaf r ≠ p.x := by
      intro hrx
      apply p.x_not_mem
      rw [← hrx]
      exact hleafB r
    apply PrimitiveTwoRetainedPositiveStratumRows.to_oneRetainedCyclePurePresentation
      g y Br (by simpa only [Br] using hz.1 r) hpow leaf a r hincidence
        hspan p.x hxBr hrx

/-- The simultaneous pure family carries an injective matrix of canonical
private witnesses at its one common inserted owner.  This is the first
cross-puncture invariant: the rows themselves, not only their deletion sets,
are pairwise distinct. -/
theorem PrimitiveTwoRetainedPositiveStratumPresentation.exchange_all_fullDeleted_cycleLeaves_to_injectivePrivateMatrix_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (p : TwoRetainedFiveWeightPresentation g y B)
    (hpres : PrimitiveTwoRetainedPositiveStratumPresentation g y B p)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (hd : 0 < d) (leaf : Fin d → Fin n)
    (hleafInj : Function.Injective leaf)
    (a : ZMod (2 ^ t * q)) (hleafB : ∀ i, leaf i ∈ B)
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y)
    (hpow : 4 < 2 ^ t) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      (∃ M : PrimitivePuncturedCyclePrivateMatrix g y
          (fun r ↦ insert p.x (B.erase (leaf r))) leaf p.x p.z,
        Function.Injective M.commonCoeff) ∨
      (∃ M : PrimitivePuncturedCyclePrivateMatrix g y
          (fun r ↦ insert p.z (B.erase (leaf r))) leaf p.z p.x,
        Function.Injective M.commonCoeff) := by
  classical
  have hxOutside : p.x ∉ Set.range leaf := by
    rintro ⟨i, hix⟩
    apply p.x_not_mem
    rw [← hix]
    exact hleafB i
  have hzOutside : p.z ∉ Set.range leaf := by
    rintro ⟨i, hiz⟩
    apply p.z_not_mem
    rw [← hiz]
    exact hleafB i
  have hcommonX :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 2 ^ t := by
    simpa using hpres.2.2.2.1
  have hcommonZ :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.z - g p.x)) = 2 ^ t := by
    have hneg : g p.z - g p.x = -(g p.x - g p.z) := by abel
    rw [hneg, map_neg, addOrderOf_neg]
    exact hcommonX
  rcases hpres.exchange_all_fullDeleted_cycleLeaves_to_purePresentations_or_three
      ht g hg hh hne hunique hno y hyq hfullOdd B p hminimal hd leaf
        hleafInj a hleafB hspan hpow with
    hthree | hx | hz
  · exact Or.inl hthree
  · right
    left
    have hincidence : ∀ r i,
        leaf i ∈ insert p.x (B.erase (leaf r)) ↔ i ≠ r := by
      intro r
      exact cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hxOutside
    obtain ⟨M⟩ := exists_primitivePuncturedCyclePrivateMatrix_of_pureFamily
      g y (fun r ↦ insert p.x (B.erase (leaf r))) leaf p.x p.z a hx.1
        hleafInj (fun r ↦ Finset.mem_insert_self _ _) hincidence hx.2
          hcommonX hpow hspan
    exact ⟨M, M.commonCoeff_injective (by omega)⟩
  · right
    right
    have hincidence : ∀ r i,
        leaf i ∈ insert p.z (B.erase (leaf r)) ↔ i ≠ r := by
      intro r
      exact cycleRange_mem_insert_erase_leaf_iff
        leaf hleafInj hleafB r hzOutside
    obtain ⟨M⟩ := exists_primitivePuncturedCyclePrivateMatrix_of_pureFamily
      g y (fun r ↦ insert p.z (B.erase (leaf r))) leaf p.z p.x a hz.1
        hleafInj (fun r ↦ Finset.mem_insert_self _ _) hincidence hz.2
          hcommonZ hpow hspan
    exact ⟨M, M.commonCoeff_injective (by omega)⟩

/-- Every positive-stratum exact-two state reaches C2 or the uniform
full-order two-retained state.  The first-stratum trivial-difference case is
handled by the primitive owner furnished by minimality. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.positiveStratum_exchange_to_fullOrder_or_three
    {t q : ℕ} [NeZero (2 ^ t * q)] (ht : 1 ≤ t)
    (g : Fin n → ZMod (2 ^ t * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ t * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ t * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ t * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ t * q → M ∣ 2 ^ t * q →
        ¬ AdmitsValidTuple n M) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ B₀ : Finset (Fin n),
        PrimitiveTwoRetainedPositiveStratumRows g y B₀ := by
  classical
  obtain ⟨p⟩ := hrows.fiveWeightPresentation g y B
  have hnormal := p.positiveStratum_completeQuotientRowNormalForm_withExchangeSeed
    ht g hg hunique hne y hyq hfullOdd B hrows hminimal
  rcases hnormal with hfirst | hhalf | hfull
  · rcases hfirst with ⟨rfl, _htrivial, b, hbprimitive⟩
    rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
        ht g hg hh hne hunique hno y hyq hfullOdd hmin hrows.1
          b.property p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
          hbprimitive hminimal with hthree | hexact
    · exact Or.inl hthree
    · exact Or.inr ⟨insert p.x (B.erase (b : Fin n)), hexact⟩
  · rcases hhalf.2 with ⟨b, _hbweight, hbprimitive⟩
    rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
        ht g hg hh hne hunique hno y hyq hfullOdd hmin hrows.1
          b.property p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
          hbprimitive hminimal with hthree | hexact
    · exact Or.inl hthree
    · exact Or.inr ⟨insert p.x (B.erase (b : Fin n)), hexact⟩
  · right
    refine ⟨B, hmin, hrows.1, hrows, p, ?_⟩
    exact hfull

/-- Lossless fifth-stratum connection of the pure-pair quotient rejoin to
uniform exchange minimization.  Exchanging the primitive half-order owner
inserts the actual missing cycle leaf, so the equality arm retains a fully
deleted cycle.  The already-full arm retains its original one-missing-leaf
orientation and presentation. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_criticalFifthStratum_exchangeRejoin
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0)
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hrTwo : 2 ≤ addOrderOf y) (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d))
    (hcycle : R.IsCycle) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 5 * q))
    (p i₀ : Fin d) (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ B₀ : Finset (Fin n),
        PrimitiveTwoRetainedPositiveStratumRows g y B₀ ∧
          ((∀ i, leaf i ∈ B₀) ∨
            (B₀ = B ∧
              ∃ pres : TwoRetainedFiveWeightPresentation g y B,
                ((leaf p = pres.x ∧ ∀ i (hi : leaf i ∈ B),
                    pres.weight ⟨leaf i, hi⟩ = -2) ∨
                  (leaf p = pres.z ∧ ∀ i (hi : leaf i ∈ B),
                    pres.weight ⟨leaf i, hi⟩ = 0)) ∧
                addOrderOf
                  ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                    (g pres.x - g pres.z)) = 32)) := by
  classical
  obtain ⟨pres, hpure, hnormal⟩ :=
    hrows.oneRetainedCycle_criticalFifthStratum_quotientRejoin
      hq g hg hcritical hunique hne y hyq hfullOdd hrTwo B hminimal leaf
        hleafInj R hcycle hRne a p i₀ hi₀ hRi₀ hleafB hdouble hspan
  rcases hnormal with hhalf | hfull
  · rcases hhalf with
      ⟨_hindex, b, hbweight, hbprimitive, hbOutside⟩
    rcases hpure with hpureX | hpureZ
    · rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
          (t := 5) (q := q) (by omega) g hg hh hne hunique hno y hyq
            hfullOdd hmin hrows.1 b.property pres.x_not_mem pres.z_not_mem
            pres.x_ne_z pres.complement_eq hbprimitive hminimal with
        hthree | hexact
      · exact Or.inl hthree
      · right
        refine ⟨insert pres.x (B.erase (b : Fin n)), hexact, Or.inl ?_⟩
        exact cycleRange_subset_insert_erase_missing leaf p hleafB hpureX.1
          hbOutside
    · have hbprimitiveX :=
        pres.primitive_otherRetained_of_weight_eq_neg_one
          (t := 5) (q := q) g y B b hbweight hbprimitive
      have hcomplementReverse : Finset.univ \ B = {pres.z, pres.x} := by
        simpa only [pair_comm] using pres.complement_eq
      rcases exists_minimalCyclicKernelTransversal_exchange_fixed_fullOrder_or_three
          (t := 5) (q := q) (by omega) g hg hh hne hunique hno y hyq
            hfullOdd hmin hrows.1 b.property pres.z_not_mem pres.x_not_mem
            pres.x_ne_z.symm hcomplementReverse hbprimitiveX hminimal with
        hthree | hexact
      · exact Or.inl hthree
      · right
        refine ⟨insert pres.z (B.erase (b : Fin n)), hexact, Or.inl ?_⟩
        exact cycleRange_subset_insert_erase_missing leaf p hleafB hpureZ.1
          hbOutside
  · right
    have hstate : PrimitiveTwoRetainedPositiveStratumRows g y B := by
      refine ⟨hmin, hrows.1, hrows, pres, ?_⟩
      simpa using hfull
    exact ⟨B, hstate, Or.inr ⟨rfl, pres, hpure, hfull.1⟩⟩

/-- Presentation-aligned fifth-stratum terminal.  Both the exchanged
fully-deleted cycle and the unexchanged one-retained pure cycle now expose
the very presentation that carries the full-order exact two-lift rows. -/
theorem TwoRetainedMinimalCyclicKernelFiveWeightRows.oneRetainedCycle_criticalFifthStratum_alignedExchangeRejoin
    {q : ℕ} [NeZero (2 ^ 5 * q)] (hq : Odd q)
    (g : Fin n → ZMod (2 ^ 5 * q)) (hg : ValidTuple g)
    (hcritical : 2 ^ 5 * q < stratumBound n 5)
    {h : ZMod (2 ^ 5 * q)} (hh : h + h = 0)
    (hunique : ∀ u : ZMod (2 ^ 5 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 5 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hrTwo : 2 ≤ addOrderOf y) (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hrows : TwoRetainedMinimalCyclicKernelFiveWeightRows g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 5 * q → M ∣ 2 ^ 5 * q →
        ¬ AdmitsValidTuple n M)
    {d : ℕ} (leaf : Fin d → Fin n) (hleafInj : Function.Injective leaf)
    (R : Equiv.Perm (Fin d))
    (hcycle : R.IsCycle) (hRne : ∀ i, R i ≠ i)
    (a : ZMod (2 ^ 5 * q))
    (p i₀ : Fin d) (hi₀ : i₀ ≠ p) (hRi₀ : R i₀ ≠ p)
    (hleafB : ∀ i, leaf i ∈ B ↔ i ≠ p)
    (hdouble : ∀ i,
      g (leaf (R i)) - a = (2 : ℤ) • (g (leaf i) - a))
    (hspan : AddSubgroup.closure
      (Set.range (fun i ↦ g (leaf i) - a)) = AddSubgroup.zmultiples y) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      ∃ B₀ : Finset (Fin n),
        ∃ pres : TwoRetainedFiveWeightPresentation g y B₀,
          PrimitiveTwoRetainedPositiveStratumPresentation g y B₀ pres ∧
            ((∃ hleafB₀ : ∀ i, leaf i ∈ B₀,
                ∀ i j,
                  pres.weight ⟨leaf i, hleafB₀ i⟩ =
                    pres.weight ⟨leaf j, hleafB₀ j⟩) ∨
              (B₀ = B ∧
                ((leaf p = pres.x ∧ ∀ i (hi : leaf i ∈ B₀),
                    pres.weight ⟨leaf i, hi⟩ = -2) ∨
                  (leaf p = pres.z ∧ ∀ i (hi : leaf i ∈ B₀),
                    pres.weight ⟨leaf i, hi⟩ = 0)))) := by
  classical
  rcases hrows.oneRetainedCycle_criticalFifthStratum_exchangeRejoin
      hq g hg hcritical hh hunique hne hno y hyq hfullOdd hrTwo B hmin
        hminimal leaf hleafInj R hcycle hRne a p i₀ hi₀ hRi₀ hleafB
          hdouble hspan with
    hthree | ⟨B₀, hstate, hgeometry⟩
  · exact Or.inl hthree
  · right
    rcases hgeometry with hall | ⟨hB₀, pres, hpure, horder⟩
    · obtain ⟨pres, hpres, hconstant⟩ :=
        hstate.fullDeletedCycle_exactPresentation
          g y B₀ (by norm_num) (by omega) leaf R a hall hdouble
      exact ⟨B₀, pres, hpres, Or.inl ⟨hall, hconstant⟩⟩
    · subst B₀
      have hnormal := pres.fifthStratum_quotientRowNormalForm
        g hg hunique hne y hyq hfullOdd B hrows hminimal
      rcases hnormal with hhalf | hfull
      · have hfalse : (16 : ℕ) = 32 := hhalf.1.symm.trans horder
        norm_num at hfalse
      · refine ⟨B, pres, ?_, Or.inr ⟨rfl, hpure⟩⟩
        exact ⟨hmin, hrows.1, hrows, by simpa using hfull⟩

end MinModulus
