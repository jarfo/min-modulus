/-
# Lossless leaf mode at exact Mersenne order

The capacity endpoint and the aligned leaf comparison were previously
packaged through independent existential presentations.  This file keeps one
literal primitive presentation through exchange minimization, five-color
compression, primary saturation, the critical coset split, and the exact
Mersenne collapse.

In the merged branch the saturated owner class lies in the primary union
`U`, exact Mersenne capacity gives `U = L`, and hence every owner in the
four-row monochromatic family is a cycle leaf.  The fixed-presentation leaf
location theorem then forces the common normalized leaf value to be `-2`.
The full secondary residue capacity and critical bound remain attached to
the same witnesses.  The separated branch retains its original two-coset
capacity and critical residual.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneResidual

namespace MinModulus

open Finset

variable {n : ℕ}

/-- Exact-Mersenne middle residual with leaf comparison and critical capacity
attached to one literal canonical presentation. -/
def PrimitiveMiddleExactMersenneLeafModeResidual
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S T Sfull : Finset (Fin n), ∃ k₀ w : ℤ,
      PrimitiveMiddleUniformLeafValueData
        g y B leaf p S T k₀ w ∧
      S ⊆ Sfull ∧
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 64 ∧
      16 ≤ Sfull.card ∧ Sfull ⊆ B ∧ (k₀ = -1 ∨ k₀ = 0) ∧
      (∀ b : ↥B, (b : Fin n) ∈ Sfull →
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
                (g (b : Fin n) - g p.x)) = 64))) ∧
      (let r := primitiveMiddleInsertedCoordinate p k₀
        ∀ b : ↥B,
          ((b : Fin n) ∈ Sfull ↔
            g (b : Fin n) - g r ∈ AddSubgroup.zmultiples y)) ∧
      ((∀ b : ↥B, p.weight b ≠ -4) ∨
        ∀ b : ↥B, p.weight b ≠ 2) ∧
      let r := primitiveMiddleInsertedCoordinate p k₀
      let C := insert r Sfull
      let L := (Finset.univ : Finset (Fin d)).image leaf
      let U := L ∪ C
      C.card = Sfull.card + 1 ∧
      ((U = L ∧ w = -2 ∧
          2 ^ (U.card - 1) ≤ q ∧
          (∀ b ∈ U, ∀ c ∈ U,
            g b - g c ∈ AddSubgroup.zmultiples y) ∧
          U.card + 4 ≤ B.card ∧
          5 ≤ (B \ U).card ∧
          (∀ b ∈ B \ U, ∀ c ∈ U,
            g b - g c ∉ AddSubgroup.zmultiples y) ∧
          PrimitiveSaturatedSecondaryResidueCapacity g y B U p k₀ ∧
          48 * U.card.choose (U.card / 2) < 2 ^ B.card) ∨
        ((∀ b ∈ L, ∀ c ∈ C,
            g b - g c ∉ AddSubgroup.zmultiples y) ∧
          (∀ i j : ℕ,
            d.choose i * (Sfull.card + 1).choose j ≤ q) ∧
          388960 * d.choose (d / 2) < 2 ^ B.card))

/-- At exact Mersenne order, a windowed primitive middle family either
enters C2, or reaches a lossless critical residual in which the merged leaf
mode is forced to `-2`. -/
theorem PrimitiveMiddleWindowedExchangeFamily.three_or_exactMersenneLeafMode
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
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hfamily : PrimitiveMiddleWindowedExchangeFamily g y B)
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
      AddSubgroup.zmultiples y)
    (hqExact : q = 2 ^ d - 1) :
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      PrimitiveMiddleExactMersenneLeafModeResidual g y B leaf := by
  classical
  rcases hfamily with
    ⟨p, S, k₀, hprimitive, hScard, hSsub, hmiddle, hgeometry, hwindow⟩
  by_cases hthree :
      ∃ b : ↥B, (b : Fin n) ∈ S ∧
        ∃ B₀ : Finset (Fin n),
          MinimalCyclicKernelSupportTransversal g y B₀ ∧
            3 ≤ n - B₀.card
  · left
    obtain ⟨_b, _hbS, B₀, hB₀⟩ := hthree
    exact ⟨B₀, hB₀⟩
  · right
    have hstates : ∀ b : ↥B, (b : Fin n) ∈ S →
        PrimitiveTwoRetainedSixthStratumRows g y
          (middleExchangeSet g y p k₀ b) := by
      intro b hbS
      have hrow := hgeometry b hbS
      rcases hrow.2 with hminus | hzero
      · rcases exists_minimalCyclicKernelTransversal_exchange_fixed_primitive_or_three
          g hg hh hne hunique hno y hyq hfullOdd hmin hretained
            b.property p.x_not_mem p.z_not_mem p.x_ne_z p.complement_eq
            hminus.2.2 hminimal with hB₀ | hexact
        · exact (hthree ⟨b, hbS, hB₀⟩).elim
        · simpa only [middleExchangeSet, hminus.1, if_true] using hexact
      · have hcomplementReverse : Finset.univ \ B = {p.z, p.x} := by
          simpa only [pair_comm] using p.complement_eq
        rcases exists_minimalCyclicKernelTransversal_exchange_fixed_primitive_or_three
            g hg hh hne hunique hno y hyq hfullOdd hmin hretained
              b.property p.z_not_mem p.x_not_mem p.x_ne_z.symm
                hcomplementReverse hzero.2.2 hminimal with hB₀ | hexact
        · exact (hthree ⟨b, hbS, hB₀⟩).elim
        · have hzeroNe : k₀ ≠ -1 := by omega
          simpa only [middleExchangeSet, hzeroNe, if_false] using hexact
    have hrich : ∀ b : ↥B, (b : Fin n) ∈ S →
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
                (b : Fin n) p.x p.z leaf)) := by
      intro b hbS
      have hrow := hgeometry b hbS
      have hstate := hstates b hbS
      have hincidence :=
        primitiveMiddleExchange_leafIncidence
          g y p k₀ b hrow.2 leaf hleaf base hspan hleafIncidence
      have hterminal :
          TwoRetainedSixthStratumLeafTerminal
            (middleExchangeSet g y p k₀ b) leaf :=
        hstate.2.2.1.sixthStratum_leafTerminal
          g hg hunique hne y hyq (middleExchangeSet g y p k₀ b)
            hminimal hd leaf R hRne base hincidence hdouble hspan
      have haligned :=
        alignedPrimitiveExchangeLeafTerminal_of_middleExchange
          g hg hunique hne y hyq hfullOdd p k₀ b hrow.2 hstate
            hminimal hd leaf hleaf R hRne base hleafIncidence
              hdouble hspan
      exact ⟨hrow.1, hrow.2, hstate, hterminal, haligned⟩
    obtain ⟨T, w, hdata⟩ :=
      exists_primitiveMiddleUniformLeafValueData
        g y B leaf (by omega) p S k₀ hScard hSsub hmiddle hrich
    obtain ⟨Sfull, hprimitiveFull, hSsubset, hScardFull,
        hSsubFull, hrowsFull, hcomplete⟩ :=
      exists_primitiveMiddleSaturatedExtension
        g y B hyq hfullOdd p S k₀ hScard hSsub hmiddle hgeometry
    have hsplit :=
      primitiveMiddleWindowedCriticalCosetSplit_of_fixedPresentation
        g hg y hyq hfullOdd B hretained hcritical p Sfull k₀
          hprimitiveFull hScardFull hSsubFull hmiddle hcomplete hwindow
          (by omega) leaf hleaf base hspan
    let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
    let C : Finset (Fin n) := insert r Sfull
    let L : Finset (Fin n) :=
      (Finset.univ : Finset (Fin d)).image leaf
    let U : Finset (Fin n) := L ∪ C
    change C.card = Sfull.card + 1 ∧
      ((2 ^ (U.card - 1) ≤ q ∧
          (∀ b ∈ U, ∀ c ∈ U,
            g b - g c ∈ AddSubgroup.zmultiples y) ∧
          U.card + 4 ≤ B.card ∧
          5 ≤ (B \ U).card ∧
          (∀ b ∈ B \ U, ∀ c ∈ U,
            g b - g c ∉ AddSubgroup.zmultiples y) ∧
          PrimitiveSaturatedSecondaryResidueCapacity g y B U p k₀ ∧
          48 * U.card.choose (U.card / 2) < 2 ^ B.card) ∨
        ((∀ b ∈ L, ∀ c ∈ C,
            g b - g c ∉ AddSubgroup.zmultiples y) ∧
          (∀ i j : ℕ,
            d.choose i * (Sfull.card + 1).choose j ≤ q) ∧
          388960 * d.choose (d / 2) < 2 ^ B.card)) at hsplit
    rcases hsplit with ⟨hCcard, hmerged | hdistinct⟩
    · rcases hmerged with
        ⟨hUcap, hUcoset, hUgap, hfive, hseparated,
          hsecondary, hcriticalBound⟩
      have hcapMersenne : 2 ^ (U.card - 1) ≤ 2 ^ d - 1 := by
        simpa only [hqExact] using hUcap
      have hUeq : U = L := by
        apply primaryUnion_eq_leafRange_of_exactMersenne_capacity
          leaf hleaf U
        · exact Finset.subset_union_left
        · simpa only [L] using hcapMersenne
      have hTsub : T ⊆ S := hdata.2.2.1
      have hTcard : 4 ≤ T.card := hdata.2.2.2.1
      have hTnonempty : T.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨b, hbT⟩ := hTnonempty
      have hbS : b ∈ S := hTsub hbT
      have hbSfull : b ∈ Sfull := hSsubset hbS
      have hbC : b ∈ C := Finset.mem_insert_of_mem hbSfull
      have hbU : b ∈ U := Finset.mem_union_right _ hbC
      have hbL : b ∈ L := by
        rw [← hUeq]
        exact hbU
      let bB : ↥B := ⟨b, hSsub hbS⟩
      have hlocation := hdata.locationOutcome
        g y B leaf p S T k₀ w hd hleafIncidence
      have hwMinus : w = -2 := by
        rcases hlocation with hw | hfull | hzero
        · exact hw
        · exact (hfull.2 bB hbT hbL).elim
        · rcases hzero with ⟨_hwZero, _missing, _hpunctured,
            _hmissing, hoff⟩
          exact (hoff bB hbT hbL).elim
      refine ⟨p, S, T, Sfull, k₀, w, hdata, hSsubset,
        hprimitiveFull, hScardFull, hSsubFull, hmiddle, hrowsFull,
        hcomplete, hwindow, ?_⟩
      change C.card = Sfull.card + 1 ∧
        ((U = L ∧ w = -2 ∧
            2 ^ (U.card - 1) ≤ q ∧
            (∀ b ∈ U, ∀ c ∈ U,
              g b - g c ∈ AddSubgroup.zmultiples y) ∧
            U.card + 4 ≤ B.card ∧
            5 ≤ (B \ U).card ∧
            (∀ b ∈ B \ U, ∀ c ∈ U,
              g b - g c ∉ AddSubgroup.zmultiples y) ∧
            PrimitiveSaturatedSecondaryResidueCapacity g y B U p k₀ ∧
            48 * U.card.choose (U.card / 2) < 2 ^ B.card) ∨
          ((∀ b ∈ L, ∀ c ∈ C,
              g b - g c ∉ AddSubgroup.zmultiples y) ∧
            (∀ i j : ℕ,
              d.choose i * (Sfull.card + 1).choose j ≤ q) ∧
            388960 * d.choose (d / 2) < 2 ^ B.card))
      exact ⟨hCcard, Or.inl ⟨hUeq, hwMinus, hUcap, hUcoset,
        hUgap, hfive, hseparated, hsecondary, hcriticalBound⟩⟩
    · refine ⟨p, S, T, Sfull, k₀, w, hdata, hSsubset,
        hprimitiveFull, hScardFull, hSsubFull, hmiddle, hrowsFull,
        hcomplete, hwindow, ?_⟩
      change C.card = Sfull.card + 1 ∧
        ((U = L ∧ w = -2 ∧
            2 ^ (U.card - 1) ≤ q ∧
            (∀ b ∈ U, ∀ c ∈ U,
              g b - g c ∈ AddSubgroup.zmultiples y) ∧
            U.card + 4 ≤ B.card ∧
            5 ≤ (B \ U).card ∧
            (∀ b ∈ B \ U, ∀ c ∈ U,
              g b - g c ∉ AddSubgroup.zmultiples y) ∧
            PrimitiveSaturatedSecondaryResidueCapacity g y B U p k₀ ∧
            48 * U.card.choose (U.card / 2) < 2 ^ B.card) ∨
          ((∀ b ∈ L, ∀ c ∈ C,
              g b - g c ∉ AddSubgroup.zmultiples y) ∧
            (∀ i j : ℕ,
              d.choose i * (Sfull.card + 1).choose j ≤ q) ∧
            388960 * d.choose (d / 2) < 2 ^ B.card))
      exact ⟨hCcard, Or.inr hdistinct⟩

end MinModulus
