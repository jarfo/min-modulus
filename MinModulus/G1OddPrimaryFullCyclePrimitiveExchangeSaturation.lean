/-
# Saturating the primitive middle owner class

The sixteen-owner middle family was initially retained only as a large
subfamily.  Its defining parallelism actually determines a complete coset of
the odd kernel among all deleted owners.  Enlarge the selected set to that
whole fiber.  Primitive order sixty-four and the four-value canonical
parameter interval show that every newly included owner has the same middle
parameter and therefore the same exchange geometry.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeLeafLocation

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The old retained coordinate inserted in every middle exchange. -/
def primitiveMiddleInsertedCoordinate
    {q : ℕ} {g : Fin n → ZMod (2 ^ 6 * q)}
    {y : ZMod (2 ^ 6 * q)} {B : Finset (Fin n)}
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) : Fin n :=
  if k₀ = -1 then p.x else p.z

/-- The retained difference in every primitive middle family has quotient
order sixty-four. -/
theorem PrimitiveMiddleExchangeFamily.retainedDifference_order_eq
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hfamily : PrimitiveMiddleExchangeFamily g y B) :
    ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 64 := by
  classical
  rcases hfamily with
    ⟨p, S, k₀, hScard, _hSsub, hmiddle, hrows⟩
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b, hbS⟩ := hSnonempty
  have hb := hrows ⟨b, _hSsub hbS⟩ hbS
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
    AddSubgroup.zmultiples y
  let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
    QuotientAddGroup.mk' H
  refine ⟨p, ?_⟩
  rcases hmiddle with hk | hk
  · rcases hb.2 with hminus | hzero
    · have hzeroDiff : pi (g b - g p.x) = 0 :=
        (QuotientAddGroup.eq_zero_iff _).2 hminus.2.1
      have hdecomp : g b - g p.z =
          (g b - g p.x) + (g p.x - g p.z) := by abel
      have horder := hminus.2.2
      rw [hdecomp, map_add, hzeroDiff, zero_add] at horder
      simpa only [pi, H] using horder
    · omega
  · rcases hb.2 with hminus | hzero
    · omega
    · have hzeroDiff : pi (g b - g p.z) = 0 :=
        (QuotientAddGroup.eq_zero_iff _).2 hzero.2.1
      have hdecomp : g b - g p.x =
          (g b - g p.z) - (g p.x - g p.z) := by abel
      have horder := hzero.2.2
      rw [hdecomp, map_sub, hzeroDiff, zero_sub, addOrderOf_neg] at horder
      simpa only [pi, H] using horder

/-- A primitive middle family whose selected set is the complete deleted-owner
fiber parallel to the exchanged-in retained coordinate. -/
def PrimitiveMiddleSaturatedExchangeFamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n)) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S : Finset (Fin n), ∃ k₀ : ℤ,
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
      let r := primitiveMiddleInsertedCoordinate p k₀
      ∀ b : ↥B,
        ((b : Fin n) ∈ S ↔
          g (b : Fin n) - g r ∈ AddSubgroup.zmultiples y)

/-- Forget only the saturation equation. -/
theorem PrimitiveMiddleSaturatedExchangeFamily.toExchangeFamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hfamily : PrimitiveMiddleSaturatedExchangeFamily g y B) :
    PrimitiveMiddleExchangeFamily g y B := by
  rcases hfamily with
    ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows, _hcomplete⟩
  exact ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows⟩

/-- Fixed-presentation saturation of a primitive middle owner family.  The
result names the enlarged fiber while keeping the caller's literal
presentation and original owner set, so other data attached to those
witnesses can be transported through saturation. -/
theorem exists_primitiveMiddleSaturatedExtension
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (S : Finset (Fin n)) (k₀ : ℤ)
    (hScard : 16 ≤ S.card) (hSsub : S ⊆ B)
    (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hrows : ∀ b : ↥B, (b : Fin n) ∈ S →
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
              (g (b : Fin n) - g p.x)) = 64))) :
    ∃ Sfull : Finset (Fin n),
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 64 ∧
      S ⊆ Sfull ∧ 16 ≤ Sfull.card ∧ Sfull ⊆ B ∧
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
            g (b : Fin n) - g r ∈ AddSubgroup.zmultiples y)) := by
  classical
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b₀, hb₀S⟩ := hSnonempty
  have hb₀ := hrows ⟨b₀, hSsub hb₀S⟩ hb₀S
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
    AddSubgroup.zmultiples y
  let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
    QuotientAddGroup.mk' H
  have hprimitiveOrder :
      addOrderOf (pi (g p.x - g p.z)) = 64 := by
    rcases hmiddle with hk | hk
    · rcases hb₀.2 with hminus | hzero
      · have hzeroDiff : pi (g b₀ - g p.x) = 0 :=
          (QuotientAddGroup.eq_zero_iff _).2 hminus.2.1
        have hdecomp : g b₀ - g p.z =
            (g b₀ - g p.x) + (g p.x - g p.z) := by abel
        have horder := hminus.2.2
        rw [hdecomp, map_add, hzeroDiff, zero_add] at horder
        exact horder
      · omega
    · rcases hb₀.2 with hminus | hzero
      · omega
      · have hzeroDiff : pi (g b₀ - g p.z) = 0 :=
          (QuotientAddGroup.eq_zero_iff _).2 hzero.2.1
        have hdecomp : g b₀ - g p.x =
            (g b₀ - g p.z) - (g p.x - g p.z) := by abel
        have horder := hzero.2.2
        rw [hdecomp, map_sub, hzeroDiff, zero_sub, addOrderOf_neg] at horder
        exact horder
  have hprimitiveOrder' :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 64 := by
    simpa only [pi, H] using hprimitiveOrder
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
        g y B hyq hfullOdd hprimitiveOrder' b
    have hkEq : k = k₀ :=
      primitive_fourResidueParameter_eq_of_pairDifference_mem
        g y p.x p.z (b : Fin n) r hprimitiveOrder' k k₀
          hkMem hk₀Mem hquotient hquotientR hparallel
    refine ⟨by simpa only [hkEq] using hweight, ?_⟩
    exact primitive_middleParameter_geometry
      g y p.x p.z (b : Fin n) k₀ hprimitiveOrder'
        (by simpa only [hkEq] using hcorrected)
        (by simpa only [hkEq] using hquotient) hmiddle
  refine ⟨Sfull, hprimitiveOrder', hSsubset, hScardFull, hSsubFull,
    hrowsFull, ?_⟩
  dsimp only
  intro b
  simp only [Sfull, Finset.mem_filter, b.property, true_and, r]

/-- Enlarge any primitive middle family to its complete odd-kernel residue
fiber without losing the common parameter or any exchange geometry. -/
theorem PrimitiveMiddleExchangeFamily.toSaturated
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hfamily : PrimitiveMiddleExchangeFamily g y B) :
    PrimitiveMiddleSaturatedExchangeFamily g y B := by
  classical
  rcases hfamily with
    ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows⟩
  have hSnonempty : S.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨b₀, hb₀S⟩ := hSnonempty
  have hb₀ := hrows ⟨b₀, hSsub hb₀S⟩ hb₀S
  let H : AddSubgroup (ZMod (2 ^ 6 * q)) :=
    AddSubgroup.zmultiples y
  let pi : ZMod (2 ^ 6 * q) →+ ZMod (2 ^ 6 * q) ⧸ H :=
    QuotientAddGroup.mk' H
  have hprimitiveOrder :
      addOrderOf (pi (g p.x - g p.z)) = 64 := by
    rcases hmiddle with hk | hk
    · rcases hb₀.2 with hminus | hzero
      · have hzeroDiff : pi (g b₀ - g p.x) = 0 :=
          (QuotientAddGroup.eq_zero_iff _).2 hminus.2.1
        have hdecomp : g b₀ - g p.z =
            (g b₀ - g p.x) + (g p.x - g p.z) := by abel
        have horder := hminus.2.2
        rw [hdecomp, map_add, hzeroDiff, zero_add] at horder
        exact horder
      · omega
    · rcases hb₀.2 with hminus | hzero
      · omega
      · have hzeroDiff : pi (g b₀ - g p.z) = 0 :=
          (QuotientAddGroup.eq_zero_iff _).2 hzero.2.1
        have hdecomp : g b₀ - g p.x =
            (g b₀ - g p.z) - (g p.x - g p.z) := by abel
        have horder := hzero.2.2
        rw [hdecomp, map_sub, hzeroDiff, zero_sub, addOrderOf_neg] at horder
        exact horder
  have hprimitiveOrder' :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 64 := by
    simpa only [pi, H] using hprimitiveOrder
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
        g y B hyq hfullOdd hprimitiveOrder' b
    have hkEq : k = k₀ :=
      primitive_fourResidueParameter_eq_of_pairDifference_mem
        g y p.x p.z (b : Fin n) r hprimitiveOrder' k k₀
          hkMem hk₀Mem hquotient hquotientR hparallel
    refine ⟨by simpa only [hkEq] using hweight, ?_⟩
    exact primitive_middleParameter_geometry
      g y p.x p.z (b : Fin n) k₀ hprimitiveOrder'
        (by simpa only [hkEq] using hcorrected)
        (by simpa only [hkEq] using hquotient) hmiddle
  refine ⟨p, Sfull, k₀, hScardFull, hSsubFull, hmiddle,
    hrowsFull, ?_⟩
  dsimp only
  intro b
  simp only [Sfull, Finset.mem_filter, b.property, true_and, r]

end MinModulus
