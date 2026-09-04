/-
# A three-residue window in the primitive exact-two quotient

Canonical unit rows place every deleted coordinate at one of the four
quotient positions `{-1, 0, 1, 2}` relative to the retained pair.  The two
outer positions cannot both occur in a genuine exact-two terminal.  If they
did, exchange the coordinate at position `2` with the retained point at
position `0`.  The new retained difference is still primitive, while the
coordinate formerly at position `-1` moves to position `-2`, outside the
four-position unit-row normal form.  Thus minimizing the exchange must retain
at least three quotient coordinates.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveUnitRows

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The primitive exact-two state with its canonical unit rows and one of the
two outer normalized weights absent.  Since all weights are even, this says
that the quotient support lies in one of two overlapping three-point windows.
-/
def PrimitiveTwoRetainedSixthStratumUnitWindow
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n)) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    let H := AddSubgroup.zmultiples y
    let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
      QuotientAddGroup.mk' H
    let deltaQ := pi (g p.x - g p.z)
    addOrderOf deltaQ = 64 ∧
      (∀ b : ↥B,
        (p.coeff b (b : Fin n) = -1 ∨
          p.coeff b (b : Fin n) = 1) ∧
        ∃ k : ℤ, k ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
          p.weight b = 2 * k ∧
          g (b : Fin n) - g p.z + k • (g p.x - g p.z) ∈ H ∧
          pi (g (b : Fin n) - g p.z) = -(k • deltaQ)) ∧
      ((∀ b : ↥B, p.weight b ≠ -4) ∨
        ∀ b : ↥B, p.weight b ≠ 2)

/-- The two extreme primitive quotient residues force a transversal exchange
which strictly increases retained dimension.  Otherwise the exact-two state
already occupies only a three-residue window. -/
theorem PrimitiveTwoRetainedSixthStratumRows.unitWindow_or_three
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hstate : PrimitiveTwoRetainedSixthStratumRows g y B) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      PrimitiveTwoRetainedSixthStratumUnitWindow g y B := by
  classical
  obtain ⟨p, hprimitive, hunit⟩ :=
    hstate.exists_canonicalUnitRows g y B hyq hfullOdd
  by_cases hleft : ∃ bminus : ↥B, p.weight bminus = -4
  · obtain ⟨bminus, hbminusWeight⟩ := hleft
    by_cases hright : ∃ bplus : ↥B, p.weight bplus = 2
    · obtain ⟨bplus, hbplusWeight⟩ := hright
      let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
        AddSubgroup.zmultiples y
      let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
        QuotientAddGroup.mk' H
      let deltaQ := pi (g p.x - g p.z)
      have hprimitive' : addOrderOf deltaQ = 64 := by
        simpa only [deltaQ, pi, H] using hprimitive
      obtain ⟨_hbminusOwner, kminus, hkminusMem, hkminusWeight,
          _hbminusCorrected, hbminusQ⟩ := hunit bminus
      have hkminus : kminus = -2 := by
        rw [hbminusWeight] at hkminusWeight
        omega
      obtain ⟨_hbplusOwner, kplus, hkplusMem, hkplusWeight,
          _hbplusCorrected, hbplusQ⟩ := hunit bplus
      have hkplus : kplus = 1 := by
        rw [hbplusWeight] at hkplusWeight
        omega
      have hbminusNePlus : (bminus : Fin n) ≠ (bplus : Fin n) := by
        intro heq
        have hweightEq : p.weight bminus = p.weight bplus := by
          congr 1
          exact Subtype.ext heq
        rw [hbminusWeight, hbplusWeight] at hweightEq
        omega
      have hbminusXQ :
          pi (g (bminus : Fin n) - g p.x) = deltaQ := by
        have hdecomp :
            g (bminus : Fin n) - g p.x =
              (g (bminus : Fin n) - g p.z) - (g p.x - g p.z) := by
          abel
        rw [hdecomp, map_sub, hbminusQ, hkminus]
        dsimp only [deltaQ]
        module
      have hbminusXPrimitive :
          addOrderOf (pi (g (bminus : Fin n) - g p.x)) = 64 := by
        rw [hbminusXQ]
        exact hprimitive'
      have hbminusXNotMem :
          g (bminus : Fin n) - g p.x ∉ AddSubgroup.zmultiples y := by
        intro hmem
        have hzero : pi (g (bminus : Fin n) - g p.x) = 0 :=
          (QuotientAddGroup.eq_zero_iff _).2 hmem
        rw [hzero] at hbminusXPrimitive
        norm_num at hbminusXPrimitive
      have hcomplementReverse : Finset.univ \ B = {p.z, p.x} := by
        simpa [pair_comm] using p.complement_eq
      let Bexchange : Finset (Fin n) :=
        insert p.z (B.erase (bminus : Fin n))
      have hBexchange : CyclicKernelSupportTransversal g y Bexchange := by
        simpa only [Bexchange] using
          cyclicKernelSupportTransversal_exchange_of_pairDifference_not_mem
            g y hstate.1.1 bminus.property p.z_not_mem p.x_not_mem
              p.x_ne_z.symm hcomplementReverse hbminusXNotMem
      obtain ⟨B₀, hB₀sub, hB₀min⟩ :=
        exists_minimalCyclicKernelSupportTransversal_subset
          g y hBexchange
      have hBexchangeCard : Bexchange.card = B.card := by
        simpa only [Bexchange] using
          card_erase_insert_retained_eq bminus.property p.z_not_mem
      have hB₀card : B₀.card ≤ B.card := by
        calc
          B₀.card ≤ Bexchange.card := Finset.card_le_card hB₀sub
          _ = B.card := hBexchangeCard
      by_cases hstrict : B₀.card < B.card
      · left
        refine ⟨B₀, hB₀min, ?_⟩
        have hBcard : B.card ≤ n := by
          simpa using Finset.card_le_univ B
        have hretained := hstate.2.1
        omega
      · have hB₀cardEq : B₀.card = B.card := by omega
        have hB₀eq : B₀ = Bexchange := by
          apply Finset.eq_of_subset_of_card_le hB₀sub
          rw [hBexchangeCard, hB₀cardEq]
        have hretained₀ : n - B₀.card = 2 := by
          rw [hB₀cardEq]
          exact hstate.2.1
        have hcomplement₀ :
            Finset.univ \ B₀ = {(bminus : Fin n), p.x} := by
          rw [hB₀eq]
          simpa only [Bexchange] using
            complement_erase_insert_retained bminus.property
              p.z_not_mem p.x_not_mem p.x_ne_z.symm hcomplementReverse
        have hbminusNotB₀ : (bminus : Fin n) ∉ B₀ := by
          have : (bminus : Fin n) ∈ Finset.univ \ B₀ := by
            rw [hcomplement₀]
            simp
          exact (Finset.mem_sdiff.mp this).2
        have hpXNotB₀ : p.x ∉ B₀ := by
          have : p.x ∈ Finset.univ \ B₀ := by
            rw [hcomplement₀]
            simp
          exact (Finset.mem_sdiff.mp this).2
        obtain ⟨p₀, hp₀x, hp₀z⟩ :=
          exists_twoRetainedCanonicalPrivatePresentation
            g y hB₀min hretained₀ (bminus : Fin n) p.x
              hbminusNotB₀ hpXNotB₀ (by
                exact fun heq ↦ p.x_not_mem (heq ▸ bminus.property))
              hcomplement₀
        have hprimitive₀ :
            let H₀ := AddSubgroup.zmultiples y
            let pi₀ : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H₀ :=
              QuotientAddGroup.mk' H₀
            addOrderOf (pi₀ (g p₀.x - g p₀.z)) = 64 := by
          simpa only [hp₀x, hp₀z, H, pi] using hbminusXPrimitive
        have hbplusB₀ : (bplus : Fin n) ∈ B₀ := by
          rw [hB₀eq]
          apply Finset.mem_insert_of_mem
          exact Finset.mem_erase.mpr ⟨hbminusNePlus.symm, bplus.property⟩
        let bplus₀ : ↥B₀ := ⟨(bplus : Fin n), hbplusB₀⟩
        obtain ⟨_hbplusOwner₀, k₀, hk₀Mem, _hk₀Weight,
            _hbplusCorrected₀, hbplusQ₀⟩ :=
          p₀.primitive_unitRowNormalForm g y B₀ hyq hfullOdd
            hprimitive₀ bplus₀
        have hbplusXQ : pi (g (bplus : Fin n) - g p.x) =
            (-2 : ℤ) • deltaQ := by
          have hdecomp :
              g (bplus : Fin n) - g p.x =
                (g (bplus : Fin n) - g p.z) - (g p.x - g p.z) := by
            abel
          rw [hdecomp, map_sub, hbplusQ, hkplus]
          dsimp only [deltaQ]
          module
        have hbplusQ₀' :
            pi (g (bplus : Fin n) - g p.x) =
              -(k₀ • deltaQ) := by
          simpa only [bplus₀, hp₀x, hp₀z, H, pi, deltaQ, hbminusXQ]
            using hbplusQ₀
        have hk₀Zero : (k₀ - 2) • deltaQ = 0 := by
          have heq : -(k₀ • deltaQ) = (-2 : ℤ) • deltaQ :=
            hbplusQ₀'.symm.trans hbplusXQ
          have heq' : k₀ • deltaQ = (2 : ℤ) • deltaQ := by
            apply neg_injective
            simpa only [neg_zsmul] using heq
          rw [sub_zsmul, heq']
          exact add_neg_cancel _
        have hk₀Dvd : (64 : ℤ) ∣ k₀ - 2 := by
          have hdvd : (addOrderOf deltaQ : ℤ) ∣ k₀ - 2 :=
            addOrderOf_dvd_iff_zsmul_eq_zero.mpr hk₀Zero
          norm_num [hprimitive'] at hdvd
          exact hdvd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk₀Mem
        rcases hk₀Dvd with ⟨a, ha⟩
        omega
    · right
      refine ⟨p, hprimitive, hunit, Or.inr ?_⟩
      intro b hb
      exact hright ⟨b, hb⟩
  · right
    refine ⟨p, hprimitive, hunit, Or.inl ?_⟩
    intro b hb
    exact hleft ⟨b, hb⟩

end MinModulus
