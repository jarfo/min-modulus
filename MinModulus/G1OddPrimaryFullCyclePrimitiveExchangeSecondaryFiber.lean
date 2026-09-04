/-
# A secondary residue fiber outside the saturated primitive class

The primitive unit-window alternative is global: one of the two extreme
quotient parameters is absent from every deleted owner.  Preserve that fact
through the concentrated middle-family projection.  If five deleted owners
are separated from the saturated middle coset, their parameters avoid both
the saturated middle value and the globally absent extreme.  Only two values
remain, so three of the five owners occupy a second common odd-kernel coset.

This is the first iteration of the residue-fiber argument.  It replaces an
unstructured five-owner reservoir by a certified secondary coset of size at
least three, with every canonical private row retained.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeCosetCritical
import Mathlib.Combinatorics.Pigeonhole

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The concentrated middle family with the global three-residue window and
the primitive quotient presentation retained. -/
def PrimitiveMiddleWindowedExchangeFamily
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
      ((∀ b : ↥B, p.weight b ≠ -4) ∨
        ∀ b : ↥B, p.weight b ≠ 2)

/-- Forget only the global window and the explicitly retained primitive
presentation. -/
theorem PrimitiveMiddleWindowedExchangeFamily.toExchangeFamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hfamily : PrimitiveMiddleWindowedExchangeFamily g y B) :
    PrimitiveMiddleExchangeFamily g y B := by
  rcases hfamily with
    ⟨p, S, k₀, _hprimitive, hScard, hSsub, hmiddle, hrows, _hwindow⟩
  exact ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows⟩

/-- Lossless residue-class split: in the middle arm the original global
three-residue window remains attached to the same canonical presentation. -/
theorem PrimitiveCanonicalResidueClass.middleWindowedExchange_or_outerPureHeavy
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hclass : PrimitiveCanonicalResidueClass g y B) :
    PrimitiveMiddleWindowedExchangeFamily g y B ∨
      PrimitiveOuterPureHeavyFamily g y B := by
  rcases hclass with
    ⟨p, S, k₀, hprimitive, hScard, hSsub, _hk₀Mem, hrow,
      hwindow, hsplit⟩
  rcases hsplit with hmiddle | ⟨houter, howner⟩
  · left
    refine ⟨p, S, k₀, hprimitive, hScard, hSsub, hmiddle, ?_, hwindow⟩
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

/-- A second canonical residue fiber among a prescribed set of deleted
owners.  Its parameter differs from the saturated middle parameter, it has at
least three owners, and all its owner entries lie in one odd-kernel coset. -/
def PrimitiveSecondaryResidueFiber
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B U : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) : Prop :=
  ∃ T : Finset (Fin n), ∃ k₁ : ℤ,
    3 ≤ T.card ∧ T ⊆ B \ U ∧
    k₁ ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧ k₁ ≠ k₀ ∧
    (∀ b : ↥B, (b : Fin n) ∈ T →
      (p.coeff b (b : Fin n) = -1 ∨
        p.coeff b (b : Fin n) = 1) ∧
      p.weight b = 2 * k₁ ∧
      g (b : Fin n) - g p.z + k₁ • (g p.x - g p.z) ∈
        AddSubgroup.zmultiples y ∧
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.z) =
        -(k₁ •
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z))) ∧
    ∀ b ∈ T, ∀ c ∈ T,
      g b - g c ∈ AddSubgroup.zmultiples y

/-- Five owners separated from a saturated middle coset contain three owners
in a second common residue fiber.  The proof uses only the global
three-residue window and the order-64 quotient normal form, so it is reusable
independently of the leaf presentation which supplied the five owners. -/
theorem exists_primitiveSecondaryResidueFiber_of_five_separated
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B U : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ)
    (hprimitive :
      addOrderOf
        ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g p.x - g p.z)) = 64)
    (hyq : addOrderOf y ∣ q) (hfullOdd : q / addOrderOf y = 1)
    (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hwindow :
      (∀ b : ↥B, p.weight b ≠ -4) ∨
        ∀ b : ↥B, p.weight b ≠ 2)
    (hrU : primitiveMiddleInsertedCoordinate p k₀ ∈ U)
    (hfive : 5 ≤ (B \ U).card)
    (hseparated : ∀ b ∈ B \ U, ∀ c ∈ U,
      g b - g c ∉ AddSubgroup.zmultiples y) :
    PrimitiveSecondaryResidueFiber g y B U p k₀ := by
  classical
  let rawK : Fin n → ℤ := fun b ↦
    if hb : b ∈ B then
      Classical.choose
        (p.primitive_unitRowNormalForm g y B hyq hfullOdd hprimitive
          ⟨b, hb⟩).2
    else 0
  have hkSpec : ∀ b : Fin n, ∀ hb : b ∈ B,
      rawK b ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
      p.weight ⟨b, hb⟩ = 2 * rawK b ∧
      g b - g p.z + rawK b • (g p.x - g p.z) ∈
        AddSubgroup.zmultiples y ∧
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g b - g p.z) =
        -(rawK b •
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) := by
    intro b hb
    have hnormal :=
      p.primitive_unitRowNormalForm g y B hyq hfullOdd hprimitive
        ⟨b, hb⟩
    simpa only [rawK, dif_pos hb] using Classical.choose_spec hnormal.2
  have hownerSpec : ∀ b : Fin n, ∀ hb : b ∈ B,
      p.coeff ⟨b, hb⟩ b = -1 ∨ p.coeff ⟨b, hb⟩ b = 1 := by
    intro b hb
    exact (p.primitive_unitRowNormalForm
      g y B hyq hfullOdd hprimitive ⟨b, hb⟩).1
  have hrawNe : ∀ b ∈ B \ U, rawK b ≠ k₀ := by
    intro b hbOutside hk
    have hbB := (Finset.mem_sdiff.mp hbOutside).1
    have hcorrected := (hkSpec b hbB).2.2.1
    have hparallel :
        g b - g (primitiveMiddleInsertedCoordinate p k₀) ∈
          AddSubgroup.zmultiples y := by
      rcases hmiddle with hk₀ | hk₀
      · simp only [primitiveMiddleInsertedCoordinate, hk₀, if_true]
        rw [hk, hk₀] at hcorrected
        convert hcorrected using 1
        module
      · have hk₀Ne : k₀ ≠ -1 := by omega
        simp only [primitiveMiddleInsertedCoordinate, hk₀Ne, if_false]
        rw [hk, hk₀] at hcorrected
        simpa only [zero_zsmul, add_zero] using hcorrected
    exact hseparated b hbOutside
      (primitiveMiddleInsertedCoordinate p k₀) hrU hparallel
  have extract : ∀ K : Finset ℤ,
      K.card = 2 →
      K ⊆ ({-2, -1, 0, 1} : Finset ℤ) →
      (∀ k ∈ K, k ≠ k₀) →
      (∀ b ∈ B \ U, rawK b ∈ K) →
      PrimitiveSecondaryResidueFiber g y B U p k₀ := by
    intro K hKcard hKsub hKne hmaps
    have hKnonempty : K.Nonempty := Finset.card_pos.mp (by omega)
    have hcapacity : K.card * 2 < (B \ U).card := by omega
    obtain ⟨k₁, hk₁K, hk₁card⟩ :=
      Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
        (s := B \ U) (t := K) (f := rawK) (n := 2)
          hmaps hcapacity
    let T : Finset (Fin n) :=
      (B \ U).filter (fun b ↦ rawK b = k₁)
    have hTcard : 3 ≤ T.card := by
      simp only [T] at hk₁card ⊢
      omega
    have hTsub : T ⊆ B \ U := by
      intro b hbT
      exact (Finset.mem_filter.mp hbT).1
    have hk₁Canon : k₁ ∈ ({-2, -1, 0, 1} : Finset ℤ) :=
      hKsub hk₁K
    have hk₁Ne : k₁ ≠ k₀ := hKne k₁ hk₁K
    refine ⟨T, k₁, hTcard, hTsub, hk₁Canon, hk₁Ne, ?_, ?_⟩
    · intro b hbT
      have hbOutside := hTsub hbT
      have hbB := (Finset.mem_sdiff.mp hbOutside).1
      have hkEq : rawK (b : Fin n) = k₁ :=
        (Finset.mem_filter.mp hbT).2
      have hs := hkSpec (b : Fin n) hbB
      refine ⟨hownerSpec (b : Fin n) hbB, ?_, ?_, ?_⟩
      · simpa only [hkEq] using hs.2.1
      · simpa only [hkEq] using hs.2.2.1
      · simpa only [hkEq] using hs.2.2.2
    · intro b hbT c hcT
      have hbOutside := hTsub hbT
      have hcOutside := hTsub hcT
      have hbB := (Finset.mem_sdiff.mp hbOutside).1
      have hcB := (Finset.mem_sdiff.mp hcOutside).1
      have hkb : rawK b = k₁ := (Finset.mem_filter.mp hbT).2
      have hkc : rawK c = k₁ := (Finset.mem_filter.mp hcT).2
      have hbCorrected := (hkSpec b hbB).2.2.1
      have hcCorrected := (hkSpec c hcB).2.2.1
      rw [hkb] at hbCorrected
      rw [hkc] at hcCorrected
      have hsub :=
        (AddSubgroup.zmultiples y).sub_mem hbCorrected hcCorrected
      convert hsub using 1
      module
  rcases hwindow with hnoMinusFour | hnoTwo
  · rcases hmiddle with hk₀ | hk₀
    · apply extract ({0, 1} : Finset ℤ)
      · norm_num
      · norm_num [Finset.subset_iff]
      · intro k hkK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hkK
        omega
      · intro b hbOutside
        have hbB := (Finset.mem_sdiff.mp hbOutside).1
        have hs := hkSpec b hbB
        have hnotMinusTwo : rawK b ≠ -2 := by
          intro hk
          apply hnoMinusFour ⟨b, hbB⟩
          rw [hs.2.1, hk]
          norm_num
        have hne := hrawNe b hbOutside
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs ⊢
        omega
    · apply extract ({-1, 1} : Finset ℤ)
      · norm_num
      · norm_num [Finset.subset_iff]
      · intro k hkK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hkK
        omega
      · intro b hbOutside
        have hbB := (Finset.mem_sdiff.mp hbOutside).1
        have hs := hkSpec b hbB
        have hnotMinusTwo : rawK b ≠ -2 := by
          intro hk
          apply hnoMinusFour ⟨b, hbB⟩
          rw [hs.2.1, hk]
          norm_num
        have hne := hrawNe b hbOutside
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs ⊢
        omega
  · rcases hmiddle with hk₀ | hk₀
    · apply extract ({-2, 0} : Finset ℤ)
      · norm_num
      · norm_num [Finset.subset_iff]
      · intro k hkK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hkK
        omega
      · intro b hbOutside
        have hbB := (Finset.mem_sdiff.mp hbOutside).1
        have hs := hkSpec b hbB
        have hnotOne : rawK b ≠ 1 := by
          intro hk
          apply hnoTwo ⟨b, hbB⟩
          rw [hs.2.1, hk]
          norm_num
        have hne := hrawNe b hbOutside
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs ⊢
        omega
    · apply extract ({-2, -1} : Finset ℤ)
      · norm_num
      · norm_num [Finset.subset_iff]
      · intro k hkK
        simp only [Finset.mem_insert, Finset.mem_singleton] at hkK
        omega
      · intro b hbOutside
        have hbB := (Finset.mem_sdiff.mp hbOutside).1
        have hs := hkSpec b hbB
        have hnotOne : rawK b ≠ 1 := by
          intro hk
          apply hnoTwo ⟨b, hbB⟩
          rw [hs.2.1, hk]
          norm_num
        have hne := hrawNe b hbOutside
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs ⊢
        omega

end MinModulus
