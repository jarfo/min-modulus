/-
# Every primitive middle exchange reaches the leaf terminal

The first leaf-incidence split deliberately retained an apparent all-on-leaf
arm.  That arm disappears once the middle-row geometry is kept alongside the
literal exact exchange.  If removing a selected leaf and inserting the
parallel retained coordinate would leave two missing leaves, then the other
retained coordinate is itself the old missing leaf.  Both endpoints of the
row's primitive quotient difference are therefore leaf displacements in the
odd kernel, contradicting quotient order sixty-four.

Consequently every member of the at-least-sixteen exact-exchange family has
full-or-one-missing incidence and carries the existing sixth-stratum leaf
terminal.  No separate large-cycle terminal is introduced.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeLeafIncidence

namespace MinModulus

open Finset

variable {n : ℕ}

/-- Removing one leaf from a fully present injective leaf family and
inserting a point outside the finset leaves exactly that leaf missing. -/
theorem leafIncidence_erase_full_leaf_insert_external
    {B : Finset (Fin n)} {d : ℕ} (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf) (hfull : ∀ j, leaf j ∈ B)
    (i : Fin d) {r : Fin n} (hrB : r ∉ B) :
    ∀ j, leaf j ∈ insert r (B.erase (leaf i)) ↔ j ≠ i := by
  classical
  intro j
  constructor
  · intro hj hji
    subst j
    rcases Finset.mem_insert.mp hj with hir | hiErase
    · exact hrB (hir ▸ hfull i)
    · exact (Finset.mem_erase.mp hiErase).1 rfl
  · intro hji
    have hleafNe : leaf j ≠ leaf i := by
      intro hjiLeaf
      exact hji (hleaf hjiLeaf)
    exact Finset.mem_insert_of_mem
      (Finset.mem_erase.mpr ⟨hleafNe, hfull j⟩)

/-- In a one-missing injective leaf family, filling the old missing leaf while
erasing a different leaf leaves exactly the erased leaf missing. -/
theorem leafIncidence_erase_present_leaf_insert_missing
    {B : Finset (Fin n)} {d : ℕ} (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf) {missing i : Fin d}
    (him : i ≠ missing)
    (hpunctured : ∀ j, leaf j ∈ B ↔ j ≠ missing) :
    ∀ j,
      leaf j ∈ insert (leaf missing) (B.erase (leaf i)) ↔ j ≠ i := by
  classical
  intro j
  constructor
  · intro hj hji
    subst j
    rcases Finset.mem_insert.mp hj with himLeaf | hiErase
    · exact him (hleaf himLeaf)
    · exact (Finset.mem_erase.mp hiErase).1 rfl
  · intro hji
    by_cases hjm : j = missing
    · subst j
      exact Finset.mem_insert_self _ _
    · have hleafNe : leaf j ≠ leaf i := by
        intro hjiLeaf
        exact hji (hleaf hjiLeaf)
      exact Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr
          ⟨hleafNe, (hpunctured j).mpr hjm⟩)

/-- The retained middle geometry rules out the only case in which exchanging
a selected owner could change full-or-one-missing incidence into two missing
leaves. -/
theorem primitiveMiddleExchange_leafIncidence
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) {B : Finset (Fin n)}
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
    {d : ℕ} (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (base : ZMod (2 ^ 6 * q))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y)
    (hincidence :
      (∀ i, leaf i ∈ B) ∨
        ∃ missing : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ missing) :
    (∀ i, leaf i ∈ middleExchangeSet g y p k₀ b) ∨
      ∃ missing : Fin d,
        ∀ i, leaf i ∈ middleExchangeSet g y p k₀ b ↔
          i ≠ missing := by
  classical
  by_cases hboff :
      (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf
  · rcases hgeometry with hminus | hzero
    · simpa only [middleExchangeSet, hminus.1, if_true] using
        (leafIncidence_insert_erase_of_owner_not_mem_range
          leaf hboff hincidence (r := p.x))
    · have hzeroNe : k₀ ≠ -1 := by omega
      simpa only [middleExchangeSet, hzeroNe, if_false] using
        (leafIncidence_insert_erase_of_owner_not_mem_range
          leaf hboff hincidence (r := p.z))
  · push Not at hboff
    obtain ⟨i, _, hiLeaf⟩ := Finset.mem_image.mp hboff
    rcases hincidence with hfull | ⟨missing, hpunctured⟩
    · rcases hgeometry with hminus | hzero
      · right
        refine ⟨i, ?_⟩
        simpa only [middleExchangeSet, hminus.1, if_true, hiLeaf] using
          (leafIncidence_erase_full_leaf_insert_external
            leaf hleaf hfull i p.x_not_mem)
      · have hzeroNe : k₀ ≠ -1 := by omega
        right
        refine ⟨i, ?_⟩
        simpa only [middleExchangeSet, hzeroNe, if_false, hiLeaf] using
          (leafIncidence_erase_full_leaf_insert_external
            leaf hleaf hfull i p.z_not_mem)
    · have hiB : leaf i ∈ B := by
        simpa only [hiLeaf] using b.property
      have him : i ≠ missing := (hpunctured i).mp hiB
      have hmissingNotB : leaf missing ∉ B := by
        intro hmB
        exact (hpunctured missing).mp hmB rfl
      have hmissingComplement :
          leaf missing ∈ Finset.univ \ B :=
        Finset.mem_sdiff.mpr
          ⟨Finset.mem_univ _, hmissingNotB⟩
      rw [p.complement_eq] at hmissingComplement
      have hmissingPair :
          leaf missing = p.x ∨ leaf missing = p.z := by
        simpa only [Finset.mem_insert, Finset.mem_singleton] using
          hmissingComplement
      have hiDisp :
          g (leaf i) - base ∈ AddSubgroup.zmultiples y := by
        rw [← hspan]
        exact AddSubgroup.subset_closure ⟨i, rfl⟩
      have hmissingDisp :
          g (leaf missing) - base ∈ AddSubgroup.zmultiples y := by
        rw [← hspan]
        exact AddSubgroup.subset_closure ⟨missing, rfl⟩
      rcases hgeometry with hminus | hzero
      · by_cases hxMissing : p.x = leaf missing
        · right
          refine ⟨i, ?_⟩
          simpa only [middleExchangeSet, hminus.1, if_true, hiLeaf,
            hxMissing] using
            (leafIncidence_erase_present_leaf_insert_missing
              leaf hleaf him hpunctured)
        · have hzMissing : p.z = leaf missing := by
            rcases hmissingPair with hmX | hmZ
            · exact (hxMissing hmX.symm).elim
            · exact hmZ.symm
          have hdiff :
              g (b : Fin n) - g p.z ∈
                AddSubgroup.zmultiples y := by
            have hsub :=
              (AddSubgroup.zmultiples y).sub_mem hiDisp hmissingDisp
            rw [hiLeaf] at hsub
            rw [hzMissing]
            convert hsub using 1
            module
          have hquotientZero :
              (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                  (g (b : Fin n) - g p.z) = 0 :=
            (QuotientAddGroup.eq_zero_iff _).mpr hdiff
          have horder := hminus.2.2
          rw [hquotientZero, addOrderOf_zero] at horder
          norm_num at horder
      · by_cases hzMissing : p.z = leaf missing
        · right
          refine ⟨i, ?_⟩
          have hzeroNe : k₀ ≠ -1 := by omega
          simpa only [middleExchangeSet, hzeroNe, if_false, hiLeaf,
            hzMissing] using
              (leafIncidence_erase_present_leaf_insert_missing
                leaf hleaf him hpunctured)
        · have hxMissing : p.x = leaf missing := by
            rcases hmissingPair with hmX | hmZ
            · exact hmX.symm
            · exact (hzMissing hmZ.symm).elim
          have hdiff :
              g (b : Fin n) - g p.x ∈
                AddSubgroup.zmultiples y := by
            have hsub :=
              (AddSubgroup.zmultiples y).sub_mem hiDisp hmissingDisp
            rw [hiLeaf] at hsub
            rw [hxMissing]
            convert hsub using 1
            module
          have hquotientZero :
              (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                  (g (b : Fin n) - g p.x) = 0 :=
            (QuotientAddGroup.eq_zero_iff _).mpr hdiff
          have horder := hzero.2.2
          rw [hquotientZero, addOrderOf_zero] at horder
          norm_num at horder

/-- The all-exact primitive middle family with the rowwise parallel/primitive
geometry retained alongside every literal exchanged state. -/
def PrimitiveMiddleAllExactExchangeGeometryFamily
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
                (g (b : Fin n) - g p.x)) = 64)) ∧
        PrimitiveTwoRetainedSixthStratumRows g y
          (middleExchangeSet g y p k₀ b)

/-- Assemble the middle exchanges without dropping their rowwise geometry.
Either one exchange reaches C2, or all selected literal exchanges retain both
their primitive state and the relation that made the exchange possible. -/
theorem PrimitiveMiddleExchangeFamily.three_or_allExactExchangeGeometryFamily
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
    (∃ B₀ : Finset (Fin n),
        MinimalCyclicKernelSupportTransversal g y B₀ ∧
          3 ≤ n - B₀.card) ∨
      PrimitiveMiddleAllExactExchangeGeometryFamily g y B := by
  classical
  rcases hfamily with
    ⟨p, S, k₀, hScard, hSsub, hmiddle, hrow⟩
  by_cases hthree :
      ∃ b : ↥B, (b : Fin n) ∈ S ∧
        ∃ B₀ : Finset (Fin n),
          MinimalCyclicKernelSupportTransversal g y B₀ ∧
            3 ≤ n - B₀.card
  · left
    obtain ⟨_, _, B₀, hB₀⟩ := hthree
    exact ⟨B₀, hB₀⟩
  · right
    refine ⟨p, S, k₀, hScard, hSsub, hmiddle, ?_⟩
    intro b hbS
    have hrowb := hrow b hbS
    refine ⟨hrowb.1, hrowb.2, ?_⟩
    rcases hrowb.2 with hminus | hzero
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

/-- The terminal form of the simultaneous middle family: at least sixteen
literal primitive exchanges remain, their original middle geometry is
retained, and every one carries the existing leaf terminal. -/
def PrimitiveMiddleExactExchangeLeafTerminalFamily
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
          (middleExchangeSet g y p k₀ b) leaf

/-- Every literal member of the geometry-retaining exact family reaches the
sixth-stratum leaf terminal. -/
theorem PrimitiveMiddleAllExactExchangeGeometryFamily.toLeafTerminalFamily
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    {h : ZMod (2 ^ 6 * q)}
    (hunique : ∀ u : ZMod (2 ^ 6 * q),
      u + u = 0 → u = 0 ∨ u = h)
    (hne : h ≠ 0) (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (B : Finset (Fin n))
    (hfamily : PrimitiveMiddleAllExactExchangeGeometryFamily g y B)
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
    PrimitiveMiddleExactExchangeLeafTerminalFamily g y B leaf := by
  classical
  rcases hfamily with
    ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows⟩
  refine ⟨p, S, k₀, hScard, hSsub, hmiddle, ?_⟩
  intro b hbS
  have hrow := hrows b hbS
  have hstate :
      PrimitiveTwoRetainedSixthStratumRows g y
        (middleExchangeSet g y p k₀ b) :=
    hrow.2.2
  have hincidence :=
    primitiveMiddleExchange_leafIncidence
      g y p k₀ b hrow.2.1 leaf hleaf base hspan hleafIncidence
  have hterminal :
      TwoRetainedSixthStratumLeafTerminal
        (middleExchangeSet g y p k₀ b) leaf :=
    hstate.2.2.1.sixthStratum_leafTerminal
      g hg hunique hne y hyq (middleExchangeSet g y p k₀ b)
        hminimal hd leaf R hRne base hincidence hdouble hspan
  exact ⟨hrow.1, hrow.2.1, hstate, hterminal⟩

/-- Direct family-level middle endpoint: either an exchange enters C2 or at
least sixteen explicit primitive exchanges all carry the classified leaf
terminal. -/
theorem PrimitiveMiddleExchangeFamily.three_or_exactExchangeLeafTerminalFamily
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
      PrimitiveMiddleExactExchangeLeafTerminalFamily g y B leaf := by
  rcases hfamily.three_or_allExactExchangeGeometryFamily
      g hg hh hne hunique hno y hyq hfullOdd B hmin hretained hminimal with
    hthree | hexact
  · exact Or.inl hthree
  · exact Or.inr
      (hexact.toLeafTerminalFamily
        g hg hunique hne y hyq B hminimal hd leaf hleaf R hRne base
          hleafIncidence hdouble hspan)

end MinModulus
