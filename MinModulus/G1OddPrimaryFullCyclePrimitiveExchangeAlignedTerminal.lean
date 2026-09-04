/-
# Canonically aligned terminals for every primitive middle exchange

The leaf terminal attached to an exchanged transversal is initially
existential: its two retained coordinates may be presented in either order.
For the simultaneous exchange family that loses the common geometry needed
to compare different exchanges.

Here every exchange is re-presented with the deleted owner first and the
unchanged old retained coordinate second.  The newly inserted old retained
coordinate then has normalized weight exactly -2.  The proof compares its
four-residue parameter with the deleted owner's parameter, using their
odd-kernel parallelism and the primitive order-64 retained difference.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeLeafTerminal

namespace MinModulus

open Finset

variable {n : ℕ}

/-- A leaf terminal with a prescribed orientation of its retained pair and a
prescribed inserted coordinate of weight -2. -/
def AlignedPrimitiveExchangeLeafTerminal
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (x z inserted : Fin n) {d : ℕ} (leaf : Fin d → Fin n) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ hinserted : inserted ∈ B,
      p.x = x ∧ p.z = z ∧
      addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) = 64 ∧
      p.weight ⟨inserted, hinserted⟩ = -2 ∧
      ((∃ hfull : ∀ i, leaf i ∈ B,
          ∀ i j,
            p.weight ⟨leaf i, hfull i⟩ =
              p.weight ⟨leaf j, hfull j⟩) ∨
        ∃ missing : Fin d,
          (∀ i, leaf i ∈ B ↔ i ≠ missing) ∧
          ((leaf missing = p.x ∧
              ∀ i (hi : leaf i ∈ B),
                p.weight ⟨leaf i, hi⟩ = -2) ∨
            (leaf missing = p.z ∧
              ∀ i (hi : leaf i ∈ B),
                p.weight ⟨leaf i, hi⟩ = 0)))

/-- One primitive middle exchange has a canonical retained orientation.

For parameter -1 the new retained pair is (b,z) and the inserted coordinate
x has weight -2.  For parameter 0 the pair is (b,x) and the inserted
coordinate z has weight -2. -/
theorem alignedPrimitiveExchangeLeafTerminal_of_middleExchange
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    {B : Finset (Fin n)}
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) (b : ↥B)
    (hgeometry :
      (k₀ = -1 ∧
          g (b : Fin n) - g p.x ∈ AddSubgroup.zmultiples y ∧
          addOrderOf
            ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g (b : Fin n) - g p.z)) = 64) ∨
        (k₀ = 0 ∧
          g (b : Fin n) - g p.z ∈ AddSubgroup.zmultiples y ∧
          addOrderOf
            ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g (b : Fin n) - g p.x)) = 64))
    (hstate : PrimitiveTwoRetainedSixthStratumRows g y
      (middleExchangeSet g y p k₀ b))
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    (hd : 2 ≤ d) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hleafIncidence :
      (∀ i, leaf i ∈ B) ∨
        ∃ missing : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ missing)
    (hdouble : ∀ i,
      g (leaf (R i)) - base = (2 : ℤ) • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    (k₀ = -1 ∧
      AlignedPrimitiveExchangeLeafTerminal g y
        (middleExchangeSet g y p k₀ b) (b : Fin n) p.z p.x leaf) ∨
    (k₀ = 0 ∧
      AlignedPrimitiveExchangeLeafTerminal g y
        (middleExchangeSet g y p k₀ b) (b : Fin n) p.x p.z leaf) := by
  classical
  rcases hgeometry with hminus | hzero
  · have hk : k₀ = -1 := hminus.1
    subst k₀
    let B' : Finset (Fin n) := insert p.x (B.erase (b : Fin n))
    have hstate' : PrimitiveTwoRetainedSixthStratumRows g y B' := by
      simpa only [B', middleExchangeSet, if_true] using hstate
    have hcomp : Finset.univ \ B' = {(b : Fin n), p.z} := by
      simpa only [B'] using
        (complement_erase_insert_retained b.property
          p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq)
    have hbNeX : (b : Fin n) ≠ p.x := by
      intro hbx
      exact p.x_not_mem (hbx ▸ b.property)
    have hbNeZ : (b : Fin n) ≠ p.z := by
      intro hbz
      exact p.z_not_mem (hbz ▸ b.property)
    have hbNot : (b : Fin n) ∉ B' := by
      simp only [B', Finset.mem_insert, Finset.mem_erase, hbNeX,
        false_or, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
    have hzNot : p.z ∉ B' := by
      simp only [B', Finset.mem_insert, Finset.mem_erase,
        Ne.symm p.x_ne_z, false_or, p.z_not_mem, and_false,
        not_false_eq_true]
    obtain ⟨p', hpx, hpz⟩ :=
      exists_twoRetainedCanonicalPrivatePresentation
        g y hstate'.1 hstate'.2.1 (b : Fin n) p.z hbNot hzNot hbNeZ hcomp
    have hprimitive :
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p'.x - g p'.z)) = 64 := by
      rw [hpx, hpz]
      exact hminus.2.2
    have hxMem : p.x ∈ B' := by
      exact Finset.mem_insert_self _ _
    let xB : ↥B' := ⟨p.x, hxMem⟩
    obtain ⟨_, k, hkMem, hweight, _, hquotient⟩ :=
      p'.primitive_unitRowNormalForm
        g y B' hyq hfullOdd hprimitive xB
    have hownerQuotient :
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g (b : Fin n) - g p'.z) =
          -((-1 : ℤ) •
            (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g p'.x - g p'.z)) := by
      rw [hpx]
      module
    have hparallel :
        g p.x - g (b : Fin n) ∈ AddSubgroup.zmultiples y := by
      have hneg :=
        (AddSubgroup.zmultiples y).neg_mem hminus.2.1
      convert hneg using 1
      module
    have hkEq : k = -1 :=
      primitive_fourResidueParameter_eq_of_pairDifference_mem
        g y p'.x p'.z p.x (b : Fin n) hprimitive k (-1)
          hkMem (by norm_num) hquotient hownerQuotient hparallel
    have hxWeight : p'.weight xB = -2 := by
      rw [hweight, hkEq]
      norm_num
    have hincidence :
        (∀ i, leaf i ∈ B') ∨
          ∃ missing : Fin d, ∀ i, leaf i ∈ B' ↔ i ≠ missing := by
      simpa only [B', middleExchangeSet, if_true] using
        (primitiveMiddleExchange_leafIncidence
          g y p (-1) b (Or.inl ⟨rfl, hminus.2⟩)
            leaf hleaf base hspan hleafIncidence)
    refine Or.inl ⟨rfl, ?_⟩
    change AlignedPrimitiveExchangeLeafTerminal
      g y B' (b : Fin n) p.z p.x leaf
    refine ⟨p', hxMem, hpx, hpz, hprimitive, hxWeight, ?_⟩
    let pFive := p'.toFiveWeightPresentation g y B'
    rcases hincidence with hfull | ⟨missing, hpunctured⟩
    · left
      refine ⟨hfull, ?_⟩
      have hconstant :=
        pFive.fullDeleted_weight_constant_of_sixthStratum_minimal
          g hg hunique hne y hyq B' hstate'.2.2.1 hminimal
            (by omega) leaf R base hfull hdouble
      simpa only [pFive,
        TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
        using hconstant
    · right
      refine ⟨missing, hpunctured, ?_⟩
      have hpure :=
        pFive.oneRetained_purePair_of_two_le
          g hg hunique hne y hyq B' hstate'.2.2.1 hminimal
            hd leaf R hRne base missing hpunctured hdouble hspan
      simpa only [pFive,
        TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
        using hpure
  · have hk : k₀ = 0 := hzero.1
    subst k₀
    have hzeroNe : (0 : ℤ) ≠ -1 := by omega
    let B' : Finset (Fin n) := insert p.z (B.erase (b : Fin n))
    have hstate' : PrimitiveTwoRetainedSixthStratumRows g y B' := by
      simpa only [B', middleExchangeSet, hzeroNe, if_false] using hstate
    have hcomp : Finset.univ \ B' = {(b : Fin n), p.x} := by
      have hreverse : Finset.univ \ B = {p.z, p.x} := by
        simpa only [pair_comm] using p.complement_eq
      simpa only [B'] using
        (complement_erase_insert_retained b.property
          p.z_not_mem p.x_not_mem p.x_ne_z.symm hreverse)
    have hbNeZ : (b : Fin n) ≠ p.z := by
      intro hbz
      exact p.z_not_mem (hbz ▸ b.property)
    have hbNeX : (b : Fin n) ≠ p.x := by
      intro hbx
      exact p.x_not_mem (hbx ▸ b.property)
    have hbNot : (b : Fin n) ∉ B' := by
      simp only [B', Finset.mem_insert, Finset.mem_erase, hbNeZ,
        false_or, ne_eq, not_true_eq_false, false_and, not_false_eq_true]
    have hxNot : p.x ∉ B' := by
      simp only [B', Finset.mem_insert, Finset.mem_erase, p.x_ne_z,
        false_or, p.x_not_mem, and_false, not_false_eq_true]
    obtain ⟨p', hpx, hpz⟩ :=
      exists_twoRetainedCanonicalPrivatePresentation
        g y hstate'.1 hstate'.2.1 (b : Fin n) p.x hbNot hxNot hbNeX hcomp
    have hprimitive :
        addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p'.x - g p'.z)) = 64 := by
      rw [hpx, hpz]
      exact hzero.2.2
    have hzMem : p.z ∈ B' := by
      exact Finset.mem_insert_self _ _
    let zB : ↥B' := ⟨p.z, hzMem⟩
    obtain ⟨_, k, hkMem, hweight, _, hquotient⟩ :=
      p'.primitive_unitRowNormalForm
        g y B' hyq hfullOdd hprimitive zB
    have hownerQuotient :
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g (b : Fin n) - g p'.z) =
          -((-1 : ℤ) •
            (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g p'.x - g p'.z)) := by
      rw [hpx]
      module
    have hparallel :
        g p.z - g (b : Fin n) ∈ AddSubgroup.zmultiples y := by
      have hneg :=
        (AddSubgroup.zmultiples y).neg_mem hzero.2.1
      convert hneg using 1
      module
    have hkEq : k = -1 :=
      primitive_fourResidueParameter_eq_of_pairDifference_mem
        g y p'.x p'.z p.z (b : Fin n) hprimitive k (-1)
          hkMem (by norm_num) hquotient hownerQuotient hparallel
    have hzWeight : p'.weight zB = -2 := by
      rw [hweight, hkEq]
      norm_num
    have hincidence :
        (∀ i, leaf i ∈ B') ∨
          ∃ missing : Fin d, ∀ i, leaf i ∈ B' ↔ i ≠ missing := by
      simpa only [B', middleExchangeSet, hzeroNe, if_false] using
        (primitiveMiddleExchange_leafIncidence
          g y p 0 b (Or.inr ⟨rfl, hzero.2⟩)
            leaf hleaf base hspan hleafIncidence)
    refine Or.inr ⟨rfl, ?_⟩
    change AlignedPrimitiveExchangeLeafTerminal
      g y B' (b : Fin n) p.x p.z leaf
    refine ⟨p', hzMem, hpx, hpz, hprimitive, hzWeight, ?_⟩
    let pFive := p'.toFiveWeightPresentation g y B'
    rcases hincidence with hfull | ⟨missing, hpunctured⟩
    · left
      refine ⟨hfull, ?_⟩
      have hconstant :=
        pFive.fullDeleted_weight_constant_of_sixthStratum_minimal
          g hg hunique hne y hyq B' hstate'.2.2.1 hminimal
            (by omega) leaf R base hfull hdouble
      simpa only [pFive,
        TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
        using hconstant
    · right
      refine ⟨missing, hpunctured, ?_⟩
      have hpure :=
        pFive.oneRetained_purePair_of_two_le
          g hg hunique hne y hyq B' hstate'.2.2.1 hminimal
            hd leaf R hRne base missing hpunctured hdouble hspan
      simpa only [pFive,
        TwoRetainedCanonicalPrivatePresentation.toFiveWeightPresentation]
        using hpure

/-- The simultaneous primitive exchange family with every leaf terminal
oriented by the deleted owner and the unchanged old retained coordinate. -/
def PrimitiveMiddleAlignedExchangeLeafTerminalFamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) : Prop :=
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
                (g (b : Fin n) - g p.x)) = 64)) ∧
        PrimitiveTwoRetainedSixthStratumRows g y
          (middleExchangeSet g y p k₀ b) ∧
        TwoRetainedSixthStratumLeafTerminal
          (middleExchangeSet g y p k₀ b) leaf ∧
        ((k₀ = -1 ∧
            AlignedPrimitiveExchangeLeafTerminal g y
              (middleExchangeSet g y p k₀ b)
                (b : Fin n) p.z p.x leaf) ∨
          (k₀ = 0 ∧
            AlignedPrimitiveExchangeLeafTerminal g y
              (middleExchangeSet g y p k₀ b)
                (b : Fin n) p.x p.z leaf))

/-- Upgrade every existential leaf terminal in the simultaneous family to
the common canonical orientation. -/
theorem PrimitiveMiddleExactExchangeLeafTerminalFamily.toAlignedFamily
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n)) (leaf : Fin d → Fin n)
    (hfamily : PrimitiveMiddleExactExchangeLeafTerminalFamily g y B leaf)
    (hminimal : ∀ M : ℕ,
      0 < M → M < 2 ^ 6 * q → M ∣ 2 ^ 6 * q →
        ¬ AdmitsValidTuple n M)
    (hd : 2 ≤ d)
    (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hleafIncidence :
      (∀ i, leaf i ∈ B) ∨
        ∃ missing : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ missing)
    (hdouble : ∀ i,
      g (leaf (R i)) - base = (2 : ℤ) • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    PrimitiveMiddleAlignedExchangeLeafTerminalFamily g y B leaf := by
  classical
  rcases hfamily with
    ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows⟩
  refine ⟨p, S, k₀, hScard, hSsub, hmiddle, ?_⟩
  intro b hbS
  have hrow := hrows b hbS
  have haligned :=
    alignedPrimitiveExchangeLeafTerminal_of_middleExchange
      g hg hunique hne y hyq hfullOdd p k₀ b hrow.2.1 hrow.2.2.1
        hminimal hd leaf hleaf R hRne base hleafIncidence hdouble hspan
  exact ⟨hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2, haligned⟩

/-- Direct aligned endpoint of the primitive middle arm: either an exchange
enters C2, or at least sixteen literal exchanges share the canonical terminal
orientation needed for their global comparison. -/
theorem PrimitiveMiddleExchangeFamily.three_or_alignedExchangeLeafTerminalFamily
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
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
        ¬ AdmitsValidTuple n M)
    (hd : 2 ≤ d) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf)
    (R : Equiv.Perm (Fin d)) (hRne : ∀ i, R i ≠ i)
    (base : ZMod (2 ^ 6 * q))
    (hleafIncidence :
      (∀ i, leaf i ∈ B) ∨
        ∃ missing : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ missing)
    (hdouble : ∀ i,
      g (leaf (R i)) - base = (2 : ℤ) • (g (leaf i) - base))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      PrimitiveMiddleAlignedExchangeLeafTerminalFamily g y B leaf := by
  rcases hfamily.three_or_exactExchangeLeafTerminalFamily
      g hg hh hne hunique hno y hyq hfullOdd B hmin hretained hminimal
        hd leaf hleaf R hRne base hleafIncidence hdouble hspan with
    hthree | hterminal
  · exact Or.inl hthree
  · exact Or.inr
      (hterminal.toAlignedFamily
        g hg hunique hne y hyq hfullOdd B leaf hminimal hd hleaf
          R hRne base hleafIncidence hdouble hspan)

end MinModulus
