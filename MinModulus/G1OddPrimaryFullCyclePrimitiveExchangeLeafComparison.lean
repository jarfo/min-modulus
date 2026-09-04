/-
# A common leaf value across primitive middle exchanges

The canonical alignment makes the leaf terminal comparable across distinct
literal exchanges.  Every aligned terminal has one value, drawn from the
five normalized weight levels, on every leaf that remains in its deletion
set.  Coloring the at-least-sixteen exchanged owners by this value produces
at least four exchanges with one common leaf value.

This is a structural compression rather than a finite-instance argument: its
five colors are the global five-weight alphabet, independent of dimension,
the odd factor, and the leaf-cycle length.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeAlignedTerminal

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The fixed-presentation strengthening of an aligned terminal in which all
present leaves have one named normalized weight. -/
def UniformAlignedPrimitiveExchangeLeafTerminal
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (x z inserted : Fin n) {d : ℕ} (leaf : Fin d → Fin n)
    (w : ℤ) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ hinserted : inserted ∈ B,
      p.x = x ∧ p.z = z ∧
      addOrderOf
          ((QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) = 64 ∧
      p.weight ⟨inserted, hinserted⟩ = -2 ∧
      w ∈ twoRetainedNormalizedWeightLevels ∧
      (∀ i (hi : leaf i ∈ B), p.weight ⟨leaf i, hi⟩ = w) ∧
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

/-- Every aligned full-or-one-missing leaf terminal has a single named
weight on all leaves that remain in its deletion set. -/
theorem AlignedPrimitiveExchangeLeafTerminal.exists_uniformLeafValue
    {q d : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (x z inserted : Fin n) (leaf : Fin d → Fin n)
    (hd : 0 < d)
    (hterminal :
      AlignedPrimitiveExchangeLeafTerminal
        g y B x z inserted leaf) :
    ∃ w : ℤ,
      UniformAlignedPrimitiveExchangeLeafTerminal
        g y B x z inserted leaf w := by
  classical
  rcases hterminal with
    ⟨p, hinserted, hpx, hpz, hprimitive, hanchor, hleaf⟩
  rcases hleaf with hfull | ⟨missing, hpunctured, hpure⟩
  · rcases hfull with ⟨hleafB, hconstant⟩
    let i₀ : Fin d := ⟨0, hd⟩
    let w : ℤ := p.weight ⟨leaf i₀, hleafB i₀⟩
    have hw : w ∈ twoRetainedNormalizedWeightLevels :=
      p.weight_mem ⟨leaf i₀, hleafB i₀⟩
    refine ⟨w, p, hinserted, hpx, hpz, hprimitive, hanchor, hw, ?_, ?_⟩
    · intro i hi
      simpa only [w] using hconstant i i₀
    · exact Or.inl ⟨hleafB, hconstant⟩
  · rcases hpure with hminus | hzero
    · refine ⟨-2, p, hinserted, hpx, hpz, hprimitive, hanchor,
        ?_, hminus.2, ?_⟩
      · norm_num [twoRetainedNormalizedWeightLevels]
      · exact Or.inr ⟨missing, hpunctured, Or.inl hminus⟩
    · refine ⟨0, p, hinserted, hpx, hpz, hprimitive, hanchor,
        ?_, hzero.2, ?_⟩
      · norm_num [twoRetainedNormalizedWeightLevels]
      · exact Or.inr ⟨missing, hpunctured, Or.inr hzero⟩

/-- The uniform-value form of the two possible canonical orientations of one
middle exchange. -/
def MiddleExchangeUniformAlignedLeafTerminal
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) {B : Finset (Fin n)}
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) (b : ↥B) {d : ℕ} (leaf : Fin d → Fin n)
    (w : ℤ) : Prop :=
  (k₀ = -1 ∧
      UniformAlignedPrimitiveExchangeLeafTerminal g y
        (middleExchangeSet g y p k₀ b) (b : Fin n) p.z p.x leaf w) ∨
    (k₀ = 0 ∧
      UniformAlignedPrimitiveExchangeLeafTerminal g y
        (middleExchangeSet g y p k₀ b) (b : Fin n) p.x p.z leaf w)

/-- Forgetting only the full-versus-punctured tag of an aligned exchange
produces a uniform leaf value while preserving its canonical orientation and
inserted-coordinate anchor. -/
theorem exists_middleExchangeUniformAlignedLeafTerminal
    {q d : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) {B : Finset (Fin n)}
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) (b : ↥B) (leaf : Fin d → Fin n) (hd : 0 < d)
    (haligned :
      (k₀ = -1 ∧
        AlignedPrimitiveExchangeLeafTerminal g y
          (middleExchangeSet g y p k₀ b)
            (b : Fin n) p.z p.x leaf) ∨
      (k₀ = 0 ∧
        AlignedPrimitiveExchangeLeafTerminal g y
          (middleExchangeSet g y p k₀ b)
            (b : Fin n) p.x p.z leaf)) :
    ∃ w : ℤ,
      MiddleExchangeUniformAlignedLeafTerminal
        g y p k₀ b leaf w := by
  rcases haligned with hminus | hzero
  · obtain ⟨w, hw⟩ :=
      hminus.2.exists_uniformLeafValue
        g y (middleExchangeSet g y p k₀ b)
          (b : Fin n) p.z p.x leaf hd
    exact ⟨w, Or.inl ⟨hminus.1, hw⟩⟩
  · obtain ⟨w, hw⟩ :=
      hzero.2.exists_uniformLeafValue
        g y (middleExchangeSet g y p k₀ b)
          (b : Fin n) p.x p.z leaf hd
    exact ⟨w, Or.inr ⟨hzero.1, hw⟩⟩

/-- Lossless data carried by a named common-leaf-value subfamily. -/
def PrimitiveMiddleUniformLeafValueData
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n)
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (S T : Finset (Fin n)) (k₀ w : ℤ) : Prop :=
  16 ≤ S.card ∧ S ⊆ B ∧ T ⊆ S ∧ 4 ≤ T.card ∧
      (k₀ = -1 ∨ k₀ = 0) ∧
      w ∈ twoRetainedNormalizedWeightLevels ∧
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
                (b : Fin n) p.x p.z leaf))) ∧
      ∀ b : ↥B, (b : Fin n) ∈ T →
        MiddleExchangeUniformAlignedLeafTerminal
          g y p k₀ b leaf w

/-- A four-exchange monochromatic subfamily.  All original primitive state,
leaf-terminal, and middle-geometry data remain available on the ambient
sixteen-owner family; the named subfamily shares one fixed leaf weight. -/
def PrimitiveMiddleUniformLeafValueSubfamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S T : Finset (Fin n), ∃ k₀ w : ℤ,
      PrimitiveMiddleUniformLeafValueData g y B leaf p S T k₀ w

/-- Five-color compression of the aligned terminal family.  At least four of
the sixteen literal exchanges share one uniform leaf weight. -/
theorem PrimitiveMiddleAlignedExchangeLeafTerminalFamily.toUniformLeafValueSubfamily
    {q d : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (leaf : Fin d → Fin n) (hd : 0 < d)
    (hfamily :
      PrimitiveMiddleAlignedExchangeLeafTerminalFamily g y B leaf) :
    PrimitiveMiddleUniformLeafValueSubfamily g y B leaf := by
  classical
  rcases hfamily with
    ⟨p, S, k₀, hScard, hSsub, hmiddle, hrows⟩
  have hexists : ∀ b : ↥S, ∃ w : ℤ,
      MiddleExchangeUniformAlignedLeafTerminal g y p k₀
        (⟨(b : Fin n), hSsub b.property⟩ : ↥B) leaf w := by
    intro b
    have hrow :=
      hrows (⟨(b : Fin n), hSsub b.property⟩ : ↥B) b.property
    exact exists_middleExchangeUniformAlignedLeafTerminal
      g y p k₀ (⟨(b : Fin n), hSsub b.property⟩ : ↥B)
        leaf hd hrow.2.2.2.2
  let label : ↥S → ℤ := fun b ↦ Classical.choose (hexists b)
  have hlabelSpec : ∀ b : ↥S,
      MiddleExchangeUniformAlignedLeafTerminal g y p k₀
        (⟨(b : Fin n), hSsub b.property⟩ : ↥B)
          leaf (label b) := by
    intro b
    exact Classical.choose_spec (hexists b)
  have hlabelMem : ∀ b : ↥S,
      label b ∈ twoRetainedNormalizedWeightLevels := by
    intro b
    rcases hlabelSpec b with hminus | hzero
    · rcases hminus.2 with
        ⟨_, _, _, _, _, _, hw, _, _⟩
      exact hw
    · rcases hzero.2 with
        ⟨_, _, _, _, _, _, hw, _, _⟩
      exact hw
  have hmaps : ∀ b ∈ (Finset.univ : Finset ↥S),
      label b ∈ twoRetainedNormalizedWeightLevels := by
    intro b _
    exact hlabelMem b
  have hmul :
      twoRetainedNormalizedWeightLevels.card * 3 <
        (Finset.univ : Finset ↥S).card := by
    rw [card_twoRetainedNormalizedWeightLevels, Finset.card_univ,
      Fintype.card_coe]
    omega
  obtain ⟨w, hw, hwFiber⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (f := label) hmaps hmul
  let F : Finset ↥S :=
    (Finset.univ : Finset ↥S).filter (fun b ↦ label b = w)
  let T : Finset (Fin n) := F.image (fun b : ↥S ↦ (b : Fin n))
  have hTsub : T ⊆ S := by
    intro i hi
    change i ∈ F.image (fun b : ↥S ↦ (b : Fin n)) at hi
    obtain ⟨b, _hbF, hbi⟩ := Finset.mem_image.mp hi
    rw [← hbi]
    exact b.property
  have hTcard : 4 ≤ T.card := by
    have himage :
        T.card = F.card :=
      by
        change (F.image (fun b : ↥S ↦ (b : Fin n))).card = F.card
        exact Finset.card_image_of_injective F Subtype.coe_injective
    have hfiber : 3 < F.card := by
      simpa only [F] using hwFiber
    omega
  refine ⟨p, S, T, k₀, w, hScard, hSsub, hTsub, hTcard,
    hmiddle, hw, hrows, ?_⟩
  intro b hbT
  change (b : Fin n) ∈ F.image (fun s : ↥S ↦ (s : Fin n)) at hbT
  obtain ⟨s, hsF, hsb⟩ := Finset.mem_image.mp hbT
  have hlabelEq : label s = w := by
    exact (Finset.mem_filter.mp hsF).2
  have hspec := hlabelSpec s
  rw [hlabelEq] at hspec
  have hsB :
      (⟨(s : Fin n), hSsub s.property⟩ : ↥B) = b := by
    exact Subtype.ext hsb
  simpa only [hsB] using hspec

end MinModulus
