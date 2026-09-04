/-
# Lossless residue concentration in the primitive exact-two terminal

The short-profile argument produces sixteen deleted owners in one coset of
the odd kernel, but its abstract corrected-row state no longer carries the
canonical private witnesses.  This module rejoins the two descriptions.

For canonical unit rows the quotient parameter belongs to the four-element
interval `{-2,-1,0,1}`.  Two owners in one odd-kernel coset have parameters
congruent modulo the primitive order `64`; the interval is too short for two
distinct representatives.  Hence the entire sixteen-owner class has one
exact parameter.  If that parameter is outer (`-2` or `1`), the witness floor
forces every canonical owner coefficient to be `-1`.  Thus the next exchange
or pure-heavy split retains all raw witness data rather than reconstructing
it after the fact.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveShortProfile

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- In a primitive order-64 quotient, two parameters in the canonical
four-value interval are equal as soon as their owner entries differ by an
element of the odd kernel. -/
theorem primitive_fourResidueParameter_eq_of_pairDifference_mem
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (x z b c : Fin n)
    (hprimitive :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g x - g z)) =
          64)
    (kb kc : ℤ)
    (hkb : kb ∈ ({-2, -1, 0, 1} : Finset ℤ))
    (hkc : kc ∈ ({-2, -1, 0, 1} : Finset ℤ))
    (hqb :
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g b - g z) =
        -(kb •
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g x - g z)))
    (hqc :
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g c - g z) =
        -(kc •
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g x - g z)))
    (hdiff : g b - g c ∈ AddSubgroup.zmultiples y) :
    kb = kc := by
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) := AddSubgroup.zmultiples y
  let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
    QuotientAddGroup.mk' H
  let deltaQ := pi (g x - g z)
  have hdiffZero : pi (g b - g c) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).2 hdiff
  have hdecomp : g b - g c = (g b - g z) - (g c - g z) := by
    abel
  rw [hdecomp, map_sub] at hdiffZero
  have hqb' : pi (g b - g z) = -(kb • deltaQ) := by
    simpa only [pi, H, deltaQ] using hqb
  have hqc' : pi (g c - g z) = -(kc • deltaQ) := by
    simpa only [pi, H, deltaQ] using hqc
  rw [hqb', hqc'] at hdiffZero
  have hzero : (kc - kb) • deltaQ = 0 := by
    calc
      (kc - kb) • deltaQ = -(kb • deltaQ) - -(kc • deltaQ) := by
        module
      _ = 0 := hdiffZero
  have hdvd : (64 : ℤ) ∣ kc - kb := by
    have hdvd' : (addOrderOf deltaQ : ℤ) ∣ kc - kb :=
      addOrderOf_dvd_iff_zsmul_eq_zero.mpr hzero
    have horder : addOrderOf deltaQ = 64 := by
      simpa only [deltaQ, pi, H] using hprimitive
    norm_num [horder] at hdvd'
    exact hdvd'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkb hkc
  rcases hdvd with ⟨a, ha⟩
  rcases hkb with hkb | hkb | hkb | hkb <;>
    rcases hkc with hkc | hkc | hkc | hkc <;> omega

/-- A canonical unit row with an outer quotient parameter necessarily has
owner coefficient `-1`.  Owner coefficient `1` would force both retained
coefficients to have floor at least `-1`, restricting the parameter to
`-1` or `0`. -/
theorem TwoRetainedCanonicalPrivatePresentation.owner_eq_neg_one_of_outerParameter
    (g : Fin n → G) (y : G) (B : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (b : ↥B) (k : ℤ)
    (howner : p.coeff b (b : Fin n) = -1 ∨
      p.coeff b (b : Fin n) = 1)
    (hweight : p.weight b = 2 * k)
    (houter : k = -2 ∨ k = 1) :
    p.coeff b (b : Fin n) = -1 := by
  rcases howner with hminus | hone
  · exact hminus
  · exfalso
    have hshape := privateWitness_twoRetained_exactShape
      g (p.isWitness b) B (b : Fin n) b.property (p.zero_other b)
        p.x p.z p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
    have hxFloor := (p.isWitness b).2.1 p.x
    have hzFloor := (p.isWitness b).2.1 p.z
    have hweightDef := p.weight_eq b
    rw [hone] at hweightDef hshape
    norm_num [twoRetainedOwnerNormalization] at hweightDef
    rw [hweight] at hweightDef
    rcases houter with hk | hk <;> omega

/-- The lossless concentrated state.  It retains the canonical private
presentation, a sixteen-owner ambient coordinate set, its exact quotient
parameter, all rowwise owner signs, and the forced common negative owner sign
in the outer arm. -/
def PrimitiveCanonicalResidueClass
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n)) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S : Finset (Fin n), ∃ k₀ : ℤ,
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 64 ∧
      16 ≤ S.card ∧ S ⊆ B ∧
      k₀ ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
      (∀ b : ↥B, (b : Fin n) ∈ S →
        (p.coeff b (b : Fin n) = -1 ∨
          p.coeff b (b : Fin n) = 1) ∧
        p.weight b = 2 * k₀ ∧
        g (b : Fin n) - g p.z + k₀ • (g p.x - g p.z) ∈
          AddSubgroup.zmultiples y ∧
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g (b : Fin n) - g p.z) =
          -(k₀ •
            (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g p.x - g p.z))) ∧
      ((∀ b : ↥B, p.weight b ≠ -4) ∨
        ∀ b : ↥B, p.weight b ≠ 2) ∧
      ((k₀ = -1 ∨ k₀ = 0) ∨
        ((k₀ = -2 ∨ k₀ = 1) ∧
          ∀ b : ↥B, (b : Fin n) ∈ S →
            p.coeff b (b : Fin n) = -1))

/-- Rejoin short-profile concentration to the raw canonical unit rows.  The
sixteen-owner coset has one exact four-valued residue parameter; the outer
case also has one forced owner sign. -/
theorem PrimitiveTwoRetainedSixthStratumUnitWindow.toCanonicalResidueClass_of_critical
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hwindow : PrimitiveTwoRetainedSixthStratumUnitWindow g y B)
    (hretained : n - B.card = 2)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hcritical : 2 ^ 6 * q < stratumBound n 6) :
    PrimitiveCanonicalResidueClass g y B := by
  classical
  have hcorrected := hwindow.toCorrectedRows g hg y B
  have hlarge := hcorrected.toLargeShortProfileRows_of_critical
    g y B hretained hyq hfullOdd hcritical
  obtain ⟨S, hScard, hSsub, hcoset⟩ :=
    hlarge.exists_kernelCoset_card_sixteen g y B
  rcases hwindow with ⟨p, hprimitive, hunit, houterWindow⟩
  have hSnonempty : S.Nonempty := by
    apply Finset.card_pos.mp
    omega
  obtain ⟨base, hbaseS⟩ := hSnonempty
  let baseB : ↥B := ⟨base, hSsub hbaseS⟩
  let rawK : ↥B → ℤ := fun b ↦ Classical.choose (hunit b).2
  have hkSpec : ∀ b : ↥B,
      rawK b ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
      p.weight b = 2 * rawK b ∧
      g (b : Fin n) - g p.z + rawK b • (g p.x - g p.z) ∈
        AddSubgroup.zmultiples y ∧
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.z) =
        -(rawK b •
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) := by
    intro b
    exact Classical.choose_spec (hunit b).2
  let k₀ : ℤ := rawK baseB
  have hk₀Mem : k₀ ∈ ({-2, -1, 0, 1} : Finset ℤ) := hkSpec baseB |>.1
  have hkEq : ∀ b : ↥B, (b : Fin n) ∈ S → rawK b = k₀ := by
    intro b hbS
    exact primitive_fourResidueParameter_eq_of_pairDifference_mem
      g y p.x p.z (b : Fin n) base hprimitive (rawK b) k₀
        (hkSpec b).1 hk₀Mem (hkSpec b).2.2.2 (hkSpec baseB).2.2.2
        (hcoset (b : Fin n) hbS base hbaseS)
  have hrow : ∀ b : ↥B, (b : Fin n) ∈ S →
      (p.coeff b (b : Fin n) = -1 ∨
        p.coeff b (b : Fin n) = 1) ∧
      p.weight b = 2 * k₀ ∧
      g (b : Fin n) - g p.z + k₀ • (g p.x - g p.z) ∈
        AddSubgroup.zmultiples y ∧
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.z) =
        -(k₀ •
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) := by
    intro b hbS
    have hkb := hkEq b hbS
    refine ⟨(hunit b).1, ?_, ?_, ?_⟩
    · simpa only [hkb] using (hkSpec b).2.1
    · simpa only [hkb] using (hkSpec b).2.2.1
    · simpa only [hkb] using (hkSpec b).2.2.2
  have hsplit :
      (k₀ = -1 ∨ k₀ = 0) ∨
        ((k₀ = -2 ∨ k₀ = 1) ∧
          ∀ b : ↥B, (b : Fin n) ∈ S →
            p.coeff b (b : Fin n) = -1) := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk₀Mem
    rcases hk₀Mem with hk₀ | hk₀ | hk₀ | hk₀
    · right
      refine ⟨Or.inl hk₀, ?_⟩
      intro b hbS
      exact p.owner_eq_neg_one_of_outerParameter g y B b k₀
        (hrow b hbS).1 (hrow b hbS).2.1 (Or.inl hk₀)
    · exact Or.inl (Or.inl hk₀)
    · exact Or.inl (Or.inr hk₀)
    · right
      refine ⟨Or.inr hk₀, ?_⟩
      intro b hbS
      exact p.owner_eq_neg_one_of_outerParameter g y B b k₀
        (hrow b hbS).1 (hrow b hbS).2.1 (Or.inr hk₀)
  exact ⟨p, S, k₀, hprimitive, hScard, hSsub, hk₀Mem, hrow,
    houterWindow, hsplit⟩

end MinModulus
