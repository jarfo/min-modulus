/-
# Lossless windowed critical endpoint for the primitive middle family

The primary saturation, leaf-coset comparison, and secondary-fiber iteration
were previously available through separate existential packages.  This
module keeps one canonical private presentation throughout.  In the merged
leaf/owner-coset arm it installs the complete secondary residue capacity and
the factor-three central critical bound.  In the separated arm it retains the
original product layers and central-binomial residual.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeSecondaryCapacity

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The windowed middle family after saturating its primary deleted-owner
residue class, with the original primitive presentation retained. -/
def PrimitiveMiddleWindowedSaturatedExchangeFamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n)) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S : Finset (Fin n), ∃ k₀ : ℤ,
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 64 ∧
      16 ≤ S.card ∧ S ⊆ B ∧ (k₀ = -1 ∨ k₀ = 0) ∧
      (∀ b : ↥B, (b : Fin n) ∈ S →
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
          ((b : Fin n) ∈ S ↔
            g (b : Fin n) - g r ∈ AddSubgroup.zmultiples y)) ∧
      ((∀ b : ↥B, p.weight b ≠ -4) ∨
        ∀ b : ↥B, p.weight b ≠ 2)

/-- Forget the global window and explicitly retained primitive equation. -/
theorem PrimitiveMiddleWindowedSaturatedExchangeFamily.toSaturatedFamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hfamily : PrimitiveMiddleWindowedSaturatedExchangeFamily g y B) :
    PrimitiveMiddleSaturatedExchangeFamily g y B := by
  rcases hfamily with
    ⟨p, S, k₀, _hprimitive, hScard, hSsub, hmiddle, hrows,
      hcomplete, _hwindow⟩
  exact ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows, hcomplete⟩

/-- Saturate the primary residue class without losing the global window or
changing the canonical private presentation. -/
theorem PrimitiveMiddleWindowedExchangeFamily.toWindowedSaturated
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hfamily : PrimitiveMiddleWindowedExchangeFamily g y B) :
    PrimitiveMiddleWindowedSaturatedExchangeFamily g y B := by
  classical
  rcases hfamily with
    ⟨p, S, k₀, hprimitive, hScard, hSsub, hmiddle, hrows, hwindow⟩
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let Sfull : Finset (Fin n) :=
    B.filter (fun b ↦
      g b - g r ∈ AddSubgroup.zmultiples y)
  have hSsubFull : Sfull ⊆ B := by
    intro b hb
    exact (Finset.mem_filter.mp hb).1
  have hSsubset : S ⊆ Sfull := by
    intro b hbS
    have hb := hrows ⟨b, hSsub hbS⟩ hbS
    refine Finset.mem_filter.mpr ⟨hSsub hbS, ?_⟩
    rcases hb.2 with hminus | hzero
    · simpa only [r, primitiveMiddleInsertedCoordinate, hminus.1, if_true]
        using hminus.2.1
    · have hkNe : k₀ ≠ -1 := by omega
      simpa only [r, primitiveMiddleInsertedCoordinate, hkNe, if_false]
        using hzero.2.1
  have hScardFull : 16 ≤ Sfull.card :=
    hScard.trans (Finset.card_le_card hSsubset)
  have hk₀Mem : k₀ ∈ ({-2, -1, 0, 1} : Finset ℤ) := by
    rcases hmiddle with hk | hk <;> simp [hk]
  have hquotientR :
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y)) (g r - g p.z) =
        -(k₀ •
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) := by
    rcases hmiddle with hk | hk
    · simp [r, primitiveMiddleInsertedCoordinate, hk]
    · simp [r, primitiveMiddleInsertedCoordinate, hk]
  have hrowsFull : ∀ b : ↥B, (b : Fin n) ∈ Sfull →
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
              (g (b : Fin n) - g p.x)) = 64)) := by
    intro b hbFull
    have hparallel :
        g (b : Fin n) - g r ∈ AddSubgroup.zmultiples y :=
      (Finset.mem_filter.mp hbFull).2
    obtain ⟨_howner, k, hkMem, hweight, hcorrected, hquotient⟩ :=
      p.primitive_unitRowNormalForm
        g y B hyq hfullOdd hprimitive b
    have hkEq : k = k₀ :=
      primitive_fourResidueParameter_eq_of_pairDifference_mem
        g y p.x p.z (b : Fin n) r hprimitive k k₀
          hkMem hk₀Mem hquotient hquotientR hparallel
    refine ⟨by simpa only [hkEq] using hweight, ?_⟩
    exact primitive_middleParameter_geometry
      g y p.x p.z (b : Fin n) k₀ hprimitive
        (by simpa only [hkEq] using hcorrected)
        (by simpa only [hkEq] using hquotient) hmiddle
  refine ⟨p, Sfull, k₀, hprimitive, hScardFull, hSsubFull, hmiddle,
    hrowsFull, ?_, hwindow⟩
  dsimp only
  intro b
  simp only [Sfull, Finset.mem_filter, b.property, true_and, r]

/-- The exact windowed critical endpoint.  In the merged primary-coset arm
the complete secondary fiber and its product capacity are already installed;
the separated leaf/owner-coset arm retains the previous sharp residual. -/
def PrimitiveMiddleWindowedCriticalCosetResidual
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S : Finset (Fin n), ∃ k₀ : ℤ,
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 64 ∧
      16 ≤ S.card ∧ S ⊆ B ∧ (k₀ = -1 ∨ k₀ = 0) ∧
      (∀ b : ↥B, (b : Fin n) ∈ S →
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
          ((b : Fin n) ∈ S ↔
            g (b : Fin n) - g r ∈ AddSubgroup.zmultiples y)) ∧
      ((∀ b : ↥B, p.weight b ≠ -4) ∨
        ∀ b : ↥B, p.weight b ≠ 2) ∧
      let C := insert (primitiveMiddleInsertedCoordinate p k₀) S
      let L := (Finset.univ : Finset (Fin d)).image leaf
      let U := L ∪ C
      C.card = S.card + 1 ∧
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
          (∀ i j : ℕ, d.choose i * (S.card + 1).choose j ≤ q) ∧
          388960 * d.choose (d / 2) < 2 ^ B.card))

/-- Carry the global unit window through the complete critical coset split.
The equal-coset branch immediately extracts, saturates, and counts the
secondary residue class on the same canonical presentation. -/
theorem PrimitiveMiddleWindowedExchangeFamily.toWindowedCriticalCosetResidual
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hfamily : PrimitiveMiddleWindowedExchangeFamily g y B)
    (hd : 0 < d) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf)
    (base : ZMod (2 ^ 6 * q))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    PrimitiveMiddleWindowedCriticalCosetResidual g y B leaf := by
  classical
  have hsaturated :=
    hfamily.toWindowedSaturated g y B hyq hfullOdd
  rcases hsaturated with
    ⟨p, S, k₀, hprimitive, hScard, hSsub, hmiddle, hrows,
      hcomplete, hwindow⟩
  let r : Fin n := primitiveMiddleInsertedCoordinate p k₀
  let C : Finset (Fin n) := insert r S
  let L : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  let U : Finset (Fin n) := L ∪ C
  have hrNotB : r ∉ B := by
    rcases hmiddle with hk | hk
    · simpa only [r, primitiveMiddleInsertedCoordinate, hk, if_true]
        using p.x_not_mem
    · have hkNe : k₀ ≠ -1 := by omega
      simpa only [r, primitiveMiddleInsertedCoordinate, hkNe, if_false]
        using p.z_not_mem
  have hrNotS : r ∉ S := fun hrS ↦ hrNotB (hSsub hrS)
  have hCcard : C.card = S.card + 1 := by
    simp only [C, Finset.card_insert_of_notMem hrNotS]
  have hselected : ∀ b ∈ S,
      g b - g r ∈ AddSubgroup.zmultiples y := by
    intro b hbS
    exact (hcomplete ⟨b, hSsub hbS⟩).1 hbS
  have hCcoset : ∀ b ∈ C, ∀ c ∈ C,
      g b - g c ∈ AddSubgroup.zmultiples y := by
    intro b hbC c hcC
    rcases Finset.mem_insert.mp hbC with rfl | hbS
    · rcases Finset.mem_insert.mp hcC with rfl | hcS
      · simp
      · have hneg :=
          (AddSubgroup.zmultiples y).neg_mem (hselected c hcS)
        convert hneg using 1
        module
    · rcases Finset.mem_insert.mp hcC with rfl | hcS
      · exact hselected b hbS
      · have hsub :=
          (AddSubgroup.zmultiples y).sub_mem
            (hselected b hbS) (hselected c hcS)
        convert hsub using 1
        module
  have hleafDisp : ∀ i,
      g (leaf i) - base ∈ AddSubgroup.zmultiples y := by
    intro i
    rw [← hspan]
    exact AddSubgroup.subset_closure ⟨i, rfl⟩
  have hLcoset : ∀ b ∈ L, ∀ c ∈ L,
      g b - g c ∈ AddSubgroup.zmultiples y := by
    intro b hbL c hcL
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hbL
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hcL
    have hsub :=
      (AddSubgroup.zmultiples y).sub_mem (hleafDisp i) (hleafDisp j)
    convert hsub using 1
    module
  have hLcard : L.card = d := by
    simp only [L]
    rw [Finset.card_image_of_injective _ hleaf]
    simp
  have hLnonempty : L.Nonempty := by
    apply Finset.card_pos.mp
    rw [hLcard]
    exact hd
  have hCnonempty : C.Nonempty :=
    ⟨r, Finset.mem_insert_self _ _⟩
  have hUnonempty : U.Nonempty :=
    hLnonempty.mono Finset.subset_union_left
  have horder : addOrderOf y = q :=
    Nat.eq_of_dvd_of_div_eq_one hyq hfullOdd
  refine ⟨p, S, k₀, hprimitive, hScard, hSsub, hmiddle, hrows,
    hcomplete, hwindow, ?_⟩
  change C.card = S.card + 1 ∧
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
        (∀ i j : ℕ, d.choose i * (S.card + 1).choose j ≤ q) ∧
        388960 * d.choose (d / 2) < 2 ^ B.card))
  refine ⟨hCcard, ?_⟩
  by_cases hsame : ∃ b ∈ L, ∃ c ∈ C,
      g b - g c ∈ AddSubgroup.zmultiples y
  · left
    rcases hsame with ⟨b₀, hb₀L, c₀, hc₀C, hcross₀⟩
    have hcross : ∀ b ∈ L, ∀ c ∈ C,
        g b - g c ∈ AddSubgroup.zmultiples y := by
      intro b hbL c hcC
      have hadd :=
        (AddSubgroup.zmultiples y).add_mem
          (hLcoset b hbL b₀ hb₀L)
          ((AddSubgroup.zmultiples y).add_mem hcross₀
            (hCcoset c₀ hc₀C c hcC))
      convert hadd using 1
      module
    have hUcoset : ∀ b ∈ U, ∀ c ∈ U,
        g b - g c ∈ AddSubgroup.zmultiples y := by
      intro b hbU c hcU
      rcases Finset.mem_union.mp hbU with hbL | hbC
      · rcases Finset.mem_union.mp hcU with hcL | hcC
        · exact hLcoset b hbL c hcL
        · exact hcross b hbL c hcC
      · rcases Finset.mem_union.mp hcU with hcL | hcC
        · have hneg :=
            (AddSubgroup.zmultiples y).neg_mem (hcross c hcL b hbC)
          convert hneg using 1
          module
        · exact hCcoset b hbC c hcC
    have hcap :=
      two_pow_pred_le_addOrderOf_of_valid_kernelCoset
        g hg y U hUnonempty hUcoset
    rw [horder] at hcap
    have hgap := card_add_four_le_transversalCard_of_critical_kernelCoset
      B U hretained hcritical hUnonempty hcap
    have hrC : r ∈ C := Finset.mem_insert_self _ _
    have hrU : r ∈ U := Finset.mem_union_right _ hrC
    have hfive := five_le_card_transversal_sdiff_of_card_add_four_le
      B U hrU hrNotB hgap
    have hseparated : ∀ b ∈ B \ U, ∀ c ∈ U,
        g b - g c ∉ AddSubgroup.zmultiples y := by
      intro b hbOutside c hcU hbc
      let bB : ↥B := ⟨b, (Finset.mem_sdiff.mp hbOutside).1⟩
      have hbNotS : b ∉ S := by
        intro hbS
        apply (Finset.mem_sdiff.mp hbOutside).2
        exact Finset.mem_union_right _
          (Finset.mem_insert_of_mem hbS)
      have hbNotParallel :
          g b - g r ∉ AddSubgroup.zmultiples y := by
        intro hbParallel
        apply hbNotS
        exact (hcomplete bB).2 hbParallel
      have hcParallel :
          g c - g r ∈ AddSubgroup.zmultiples y := by
        rcases Finset.mem_union.mp hcU with hcL | hcC
        · exact hcross c hcL r hrC
        · rcases Finset.mem_insert.mp hcC with hcr | hcS
          · subst c
            simp
          · exact (hcomplete ⟨c, hSsub hcS⟩).1 hcS
      have hsum :=
        (AddSubgroup.zmultiples y).add_mem hbc hcParallel
      apply hbNotParallel
      convert hsum using 1
      module
    have hsecondary :=
      exists_primitiveSaturatedSecondaryResidueCapacity_of_five_separated
        g hg y B U p k₀ hprimitive hyq hfullOdd hmiddle hwindow
          hUnonempty hUcoset hrU hfive hseparated
    obtain ⟨_T, _hTcard, hcentral⟩ :=
      hsecondary.exists_centralCriticalBound
        g y B U p k₀ hretained hcritical
    exact ⟨hcap, hUcoset, hgap, hfive, hseparated,
      hsecondary, hcentral⟩
  · right
    have hcross : ∀ b ∈ L, ∀ c ∈ C,
        g b - g c ∉ AddSubgroup.zmultiples y := by
      intro b hbL c hcC hmem
      exact hsame ⟨b, hbL, c, hcC, hmem⟩
    have hdisjoint : Disjoint L C := by
      rw [Finset.disjoint_left]
      intro b hbL hbC
      exact hcross b hbL b hbC (by simp)
    have hcap : ∀ i j : ℕ,
        d.choose i * (S.card + 1).choose j ≤ q := by
      intro i j
      have h := choose_mul_choose_le_addOrderOf_of_disjoint_kernelCosets
        g hg y L C hLnonempty hCnonempty hdisjoint
          hLcoset hCcoset i j
      rw [hLcard, hCcard, horder] at h
      exact h
    exact ⟨hcross, hcap,
      central_leaf_product_lt_two_pow_transversalCard_of_critical
        B hretained hcritical hScard hcap⟩

/-- Direct canonical endpoint: the residue-concentration output reaches the
fully installed windowed critical residual, or the unchanged exact outer
pure-heavy family. -/
theorem PrimitiveCanonicalResidueClass.windowedCritical_or_outerPureHeavy
    {q d : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q)) (hg : ValidTuple g)
    (y : ZMod (2 ^ 6 * q))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (B : Finset (Fin n))
    (hretained : n - B.card = 2)
    (hcritical : 2 ^ 6 * q < stratumBound n 6)
    (hclass : PrimitiveCanonicalResidueClass g y B)
    (hd : 0 < d) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf)
    (base : ZMod (2 ^ 6 * q))
    (hspan : AddSubgroup.closure
        (Set.range (fun i : Fin d ↦ g (leaf i) - base)) =
      AddSubgroup.zmultiples y) :
    PrimitiveMiddleWindowedCriticalCosetResidual g y B leaf ∨
      PrimitiveOuterPureHeavyFamily g y B := by
  rcases hclass.middleWindowedExchange_or_outerPureHeavy g y B with
    hmiddle | houter
  · exact Or.inl (hmiddle.toWindowedCriticalCosetResidual
      g hg y hyq hfullOdd B hretained hcritical hd leaf hleaf base hspan)
  · exact Or.inr houter

end MinModulus
