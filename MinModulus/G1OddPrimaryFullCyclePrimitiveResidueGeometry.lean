/-
# Exchange and pure-heavy geometry of the concentrated residue class

The lossless sixteen-owner class has one parameter
`k₀ ∈ {-2,-1,0,1}`.  The middle parameters are parallel to one retained
coordinate and primitive relative to the other, so every owner supports the
existing lossless transversal exchange.  The outer parameters have exact
canonical coefficient triples `(-1,2,-1)` and `(-1,-1,2)` on
`(owner,x,z)`.  This turns the residue split into the two operational C1
interfaces needed by the next descent step.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveResidueClass

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- A middle parameter makes the owner parallel to one retained coordinate
and primitive relative to the other. -/
theorem primitive_middleParameter_geometry
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (x z b : Fin n) (k : ℤ)
    (hprimitive :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g x - g z)) =
          64)
    (hcorrected :
      g b - g z + k • (g x - g z) ∈ AddSubgroup.zmultiples y)
    (hquotient :
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g b - g z) =
        -(k •
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g x - g z)))
    (hmiddle : k = -1 ∨ k = 0) :
    (k = -1 ∧
        g b - g x ∈ AddSubgroup.zmultiples y ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g b - g z)) =
            64) ∨
      (k = 0 ∧
        g b - g z ∈ AddSubgroup.zmultiples y ∧
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g b - g x)) =
            64) := by
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) := AddSubgroup.zmultiples y
  let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
    QuotientAddGroup.mk' H
  let deltaQ := pi (g x - g z)
  have hprimitive' : addOrderOf deltaQ = 64 := by
    simpa only [deltaQ, pi, H] using hprimitive
  rcases hmiddle with hk | hk
  · left
    refine ⟨hk, ?_, ?_⟩
    · rw [hk] at hcorrected
      convert hcorrected using 1
      module
    · have hq : pi (g b - g z) = deltaQ := by
        simpa only [pi, H, deltaQ, hk, neg_zsmul, one_zsmul, neg_neg]
          using hquotient
      rw [hq]
      exact hprimitive'
  · right
    refine ⟨hk, ?_, ?_⟩
    · simpa only [hk, zero_zsmul, add_zero] using hcorrected
    · have hdecomp : g b - g x = (g b - g z) - (g x - g z) := by
        abel
      have hq : pi (g b - g x) = -deltaQ := by
        rw [hdecomp, map_sub]
        have hzero : pi (g b - g z) = 0 := by
          simpa only [pi, H, deltaQ, hk, zero_zsmul, neg_zero]
            using hquotient
        rw [hzero, zero_sub]
      rw [hq, addOrderOf_neg]
      exact hprimitive'

/-- An outer canonical row has one of the two exact pure-heavy retained
coefficient patterns. -/
theorem TwoRetainedCanonicalPrivatePresentation.outerParameter_exactShape
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (b : ↥B) (k : ℤ)
    (howner : p.coeff b (b : Fin n) = -1)
    (hweight : p.weight b = 2 * k)
    (houter : k = -2 ∨ k = 1) :
    (k = -2 ∧ p.coeff b p.x = 2 ∧ p.coeff b p.z = -1) ∨
      (k = 1 ∧ p.coeff b p.x = -1 ∧ p.coeff b p.z = 2) := by
  have hshape := privateWitness_twoRetained_exactShape
    g (p.isWitness b) B (b : Fin n) b.property (p.zero_other b)
      p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
  have hweightDef := p.weight_eq b
  rw [howner] at hshape hweightDef
  norm_num [twoRetainedOwnerNormalization] at hweightDef
  rw [hweight] at hweightDef
  rcases houter with hk | hk
  · left
    refine ⟨hk, ?_, ?_⟩ <;> omega
  · right
    refine ⟨hk, ?_, ?_⟩ <;> omega

/-- The middle residue arm with rowwise primitive exchange geometry retained
for every owner in the large class. -/
def PrimitiveMiddleExchangeFamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n)) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S : Finset (Fin n), ∃ k₀ : ℤ,
      16 ≤ S.card ∧ S ⊆ B ∧ (k₀ = -1 ∨ k₀ = 0) ∧
      ∀ b : ↥B, (b : Fin n) ∈ S →
        p.weight b = 2 * k₀ ∧
        ((k₀ = -1 ∧
            g (b : Fin n) - g p.x ∈ AddSubgroup.zmultiples y ∧
            addOrderOf
              ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (b : Fin n) - g p.z)) = 64) ∨
          (k₀ = 0 ∧
            g (b : Fin n) - g p.z ∈ AddSubgroup.zmultiples y ∧
            addOrderOf
              ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g (b : Fin n) - g p.x)) = 64))

/-- The outer residue arm with its exact common pure-heavy row pattern. -/
def PrimitiveOuterPureHeavyFamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n)) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S : Finset (Fin n), ∃ k₀ : ℤ,
      16 ≤ S.card ∧ S ⊆ B ∧ (k₀ = -2 ∨ k₀ = 1) ∧
      ∀ b : ↥B, (b : Fin n) ∈ S →
        p.weight b = 2 * k₀ ∧
        p.coeff b (b : Fin n) = -1 ∧
        ((k₀ = -2 ∧ p.coeff b p.x = 2 ∧ p.coeff b p.z = -1) ∨
          (k₀ = 1 ∧ p.coeff b p.x = -1 ∧ p.coeff b p.z = 2))

/-- The concentrated canonical residue class is exactly a large middle
exchange family or a large outer pure-heavy family. -/
theorem PrimitiveCanonicalResidueClass.middleExchange_or_outerPureHeavy
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hclass : PrimitiveCanonicalResidueClass g y B) :
    PrimitiveMiddleExchangeFamily g y B ∨
      PrimitiveOuterPureHeavyFamily g y B := by
  rcases hclass with ⟨p, S, k₀, hprimitive, hScard, hSsub, _hk₀Mem,
    hrow, hsplit⟩
  rcases hsplit with hmiddle | ⟨houter, howner⟩
  · left
    refine ⟨p, S, k₀, hScard, hSsub, hmiddle, ?_⟩
    intro b hbS
    have hr := hrow b hbS
    refine ⟨hr.2.1, ?_⟩
    exact primitive_middleParameter_geometry
      g y p.x p.z (b : Fin n) k₀ hprimitive hr.2.2.1 hr.2.2.2 hmiddle
  · right
    refine ⟨p, S, k₀, hScard, hSsub, houter, ?_⟩
    intro b hbS
    have hr := hrow b hbS
    have hownerB := howner b hbS
    refine ⟨hr.2.1, hownerB, ?_⟩
    exact p.outerParameter_exactShape g y B b k₀ hownerB hr.2.1 houter

/-- Every owner in the large middle class supports the existing lossless
primitive transversal exchange.  Minimization therefore either enters the
three-or-more-retained C2 arm or returns an exact-two primitive state, for all
members of a set of cardinality at least sixteen. -/
theorem PrimitiveMiddleExchangeFamily.exchange_each_to_primitive_or_three
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)} (hh : h + h = 0) (hne : h ≠ 0)
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hno : ¬ ∃ j : Fin n, ∀ c : Fin n → ℤ,
      Witness g h c → c j ≠ 0)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hmin : MinimalCyclicKernelSupportTransversal g y B)
    (hretained : n - B.card = 2)
    (hfamily : PrimitiveMiddleExchangeFamily g y B)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M) :
    ∃ S : Finset (Fin n),
      16 ≤ S.card ∧ S ⊆ B ∧
      ∀ b : ↥B, (b : Fin n) ∈ S →
        (∃ B₀ : Finset (Fin n),
            MinimalCyclicKernelSupportTransversal g y B₀ ∧
              3 ≤ n - B₀.card) ∨
          ∃ B₀ : Finset (Fin n),
            PrimitiveTwoRetainedSixthStratumRows g y B₀ := by
  rcases hfamily with ⟨p, S, k₀, hScard, hSsub, _hmiddle, hrow⟩
  refine ⟨S, hScard, hSsub, ?_⟩
  intro b hbS
  rcases (hrow b hbS).2 with hminus | hzero
  · exact exists_minimalCyclicKernelTransversal_exchange_primitive_or_three
      g hg hh hne hunique hno y hyq hfullOdd hmin hretained
        b.property p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
        hminus.2.2 hminimal
  · have hcomplementReverse : Finset.univ \ B = {p.z, p.x} := by
      simpa only [pair_comm] using p.complement_eq
    exact exists_minimalCyclicKernelTransversal_exchange_primitive_or_three
      g hg hh hne hunique hno y hyq hfullOdd hmin hretained
        b.property p.z_not_mem p.x_not_mem p.x_ne_z.symm hcomplementReverse
        hzero.2.2 hminimal

end MinModulus
