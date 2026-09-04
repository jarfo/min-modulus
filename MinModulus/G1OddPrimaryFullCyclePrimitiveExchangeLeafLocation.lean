/-
# Leaf-location classification of the common exchange value

The common leaf value extracted from the aligned exchange family is not an
arbitrary five-weight color once the old retained coordinates are compared
with the fixed leaf range.  If the inserted coordinate is a leaf, its
anchored weight forces the common value to be -2.  If the first retained
coordinate is a leaf, the one-missing terminal has the same conclusion.  If
the second retained coordinate is a leaf, the value is zero.

Combining these pointwise facts with the original full-or-one-missing
incidence leaves three global modes: value -2; full original incidence with
the selected four owners off the leaf range; or value zero with the unchanged
retained coordinate equal to the original missing leaf and all four owners
off the leaf range.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeLeafComparison

namespace MinModulus

open Finset

variable {n : ℕ}

/-- If the inserted coordinate is a leaf, its anchored weight fixes the
uniform leaf value at -2. -/
theorem UniformAlignedPrimitiveExchangeLeafTerminal.inserted_leafValue_eq_neg_two
    {q d : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (x z inserted : Fin n) (leaf : Fin d → Fin n) (w : ℤ)
    (hterminal :
      UniformAlignedPrimitiveExchangeLeafTerminal
        g y B x z inserted leaf w)
    (i : Fin d) (hi : leaf i = inserted) :
    w = -2 := by
  rcases hterminal with
    ⟨p, hinserted, _, _, _, hanchor, _, huniform, _⟩
  have hiB : leaf i ∈ B := by
    rw [hi]
    exact hinserted
  have hsub :
      (⟨leaf i, hiB⟩ : ↥B) = ⟨inserted, hinserted⟩ :=
    Subtype.ext hi
  calc
    w = p.weight ⟨leaf i, hiB⟩ := (huniform i hiB).symm
    _ = p.weight ⟨inserted, hinserted⟩ := by rw [hsub]
    _ = -2 := hanchor

/-- If the prescribed first retained coordinate is a leaf, it is the unique
missing leaf and the fixed-presentation pure-pair terminal forces value -2. -/
theorem UniformAlignedPrimitiveExchangeLeafTerminal.firstRetained_leafValue_eq_neg_two
    {q d : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (x z inserted : Fin n) (leaf : Fin d → Fin n) (w : ℤ)
    (hterminal :
      UniformAlignedPrimitiveExchangeLeafTerminal
        g y B x z inserted leaf w)
    (hd : 2 ≤ d) (i : Fin d) (hi : leaf i = x) :
    w = -2 := by
  classical
  rcases hterminal with
    ⟨p, _, hpx, _, _, _, _, huniform, hmode⟩
  rcases hmode with ⟨hfull, _⟩ | ⟨missing, hpunctured, hpure⟩
  · exfalso
    apply p.x_not_mem
    rw [hpx, ← hi]
    exact hfull i
  · have hiNot : leaf i ∉ B := by
      intro hiB
      apply p.x_not_mem
      rw [hpx, ← hi]
      exact hiB
    have him : i = missing := by
      by_contra him
      exact hiNot ((hpunctured i).mpr him)
    rcases hpure with hminus | hzero
    · obtain ⟨j, hjm⟩ :=
        Fintype.exists_ne_of_one_lt_card
          (by simp only [Fintype.card_fin]; omega) missing
      have hjB : leaf j ∈ B := (hpunctured j).mpr hjm
      calc
        w = p.weight ⟨leaf j, hjB⟩ := (huniform j hjB).symm
        _ = -2 := hminus.2 j hjB
    · exfalso
      apply p.x_ne_z
      calc
        p.x = x := hpx
        _ = leaf i := hi.symm
        _ = leaf missing := by rw [him]
        _ = p.z := hzero.1

/-- If the prescribed second retained coordinate is a leaf, it is the unique
missing leaf and the fixed-presentation pure-pair terminal forces value zero. -/
theorem UniformAlignedPrimitiveExchangeLeafTerminal.secondRetained_leafValue_eq_zero
    {q d : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (x z inserted : Fin n) (leaf : Fin d → Fin n) (w : ℤ)
    (hterminal :
      UniformAlignedPrimitiveExchangeLeafTerminal
        g y B x z inserted leaf w)
    (hd : 2 ≤ d) (i : Fin d) (hi : leaf i = z) :
    w = 0 := by
  classical
  rcases hterminal with
    ⟨p, _, _, hpz, _, _, _, huniform, hmode⟩
  rcases hmode with ⟨hfull, _⟩ | ⟨missing, hpunctured, hpure⟩
  · exfalso
    apply p.z_not_mem
    rw [hpz, ← hi]
    exact hfull i
  · have hiNot : leaf i ∉ B := by
      intro hiB
      apply p.z_not_mem
      rw [hpz, ← hi]
      exact hiB
    have him : i = missing := by
      by_contra him
      exact hiNot ((hpunctured i).mpr him)
    rcases hpure with hminus | hzero
    · exfalso
      apply p.x_ne_z
      calc
        p.x = leaf missing := hminus.1.symm
        _ = leaf i := by rw [him]
        _ = z := hi
        _ = p.z := hpz.symm
    · obtain ⟨j, hjm⟩ :=
        Fintype.exists_ne_of_one_lt_card
          (by simp only [Fintype.card_fin]; omega) missing
      have hjB : leaf j ∈ B := (hpunctured j).mpr hjm
      calc
        w = p.weight ⟨leaf j, hjB⟩ := (huniform j hjB).symm
        _ = 0 := hzero.2 j hjB

/-- The three global modes left after comparing the common exchange value
with the original leaf incidence. -/
def PrimitiveMiddleUniformLeafLocationOutcome
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n)
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (T : Finset (Fin n)) (k₀ w : ℤ) : Prop :=
  w = -2 ∨
    ((∀ i, leaf i ∈ B) ∧
      ∀ b : ↥B, (b : Fin n) ∈ T →
        (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf) ∨
    (w = 0 ∧
      ∃ missing : Fin d,
        (∀ i, leaf i ∈ B ↔ i ≠ missing) ∧
        ((k₀ = -1 ∧ leaf missing = p.z) ∨
          (k₀ = 0 ∧ leaf missing = p.x)) ∧
        ∀ b : ↥B, (b : Fin n) ∈ T →
          (b : Fin n) ∉ (Finset.univ : Finset (Fin d)).image leaf)

/-- The common-value data together with its exact global leaf-location mode. -/
def PrimitiveMiddleLeafLocationClassifiedSubfamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    {d : ℕ} (leaf : Fin d → Fin n) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S T : Finset (Fin n), ∃ k₀ w : ℤ,
      PrimitiveMiddleUniformLeafValueData g y B leaf p S T k₀ w ∧
      PrimitiveMiddleUniformLeafLocationOutcome
        g y B leaf p T k₀ w

/-- Exact leaf-location trichotomy for one lossless common-value datum. -/
theorem PrimitiveMiddleUniformLeafValueData.locationOutcome
    {q d : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (leaf : Fin d → Fin n)
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (S T : Finset (Fin n)) (k₀ w : ℤ)
    (hdata :
      PrimitiveMiddleUniformLeafValueData
        g y B leaf p S T k₀ w)
    (hd : 2 ≤ d)
    (hleafIncidence :
      (∀ i, leaf i ∈ B) ∨
        ∃ missing : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ missing) :
    PrimitiveMiddleUniformLeafLocationOutcome
      g y B leaf p T k₀ w := by
  classical
  rcases hdata with
    ⟨_hScard, hSsub, hTsub, hTcard, hmiddle, _hw, _hrows, huniform⟩
  let leafRange : Finset (Fin n) :=
    (Finset.univ : Finset (Fin d)).image leaf
  have hownerForces : ∀ b : ↥B, (b : Fin n) ∈ T →
      (b : Fin n) ∈ leafRange → w = -2 := by
    intro b hbT hbLeaf
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hbLeaf
    rcases huniform b hbT with hminus | hzero
    · exact hminus.2.firstRetained_leafValue_eq_neg_two
        g y (middleExchangeSet g y p k₀ b)
          (b : Fin n) p.z p.x leaf w hd i hi
    · exact hzero.2.firstRetained_leafValue_eq_neg_two
        g y (middleExchangeSet g y p k₀ b)
          (b : Fin n) p.x p.z leaf w hd i hi
  have hTnonempty : T.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  obtain ⟨b₀, hb₀T⟩ := hTnonempty
  let b₀B : ↥B := ⟨b₀, hSsub (hTsub hb₀T)⟩
  have hb₀Uniform :=
    huniform b₀B hb₀T
  rcases hleafIncidence with hfull | ⟨missing, hpunctured⟩
  · by_cases honLeaf :
        ∃ b : ↥B, (b : Fin n) ∈ T ∧ (b : Fin n) ∈ leafRange
    · left
      obtain ⟨b, hbT, hbLeaf⟩ := honLeaf
      exact hownerForces b hbT hbLeaf
    · right
      left
      refine ⟨hfull, ?_⟩
      intro b hbT hbLeaf
      exact honLeaf ⟨b, hbT, hbLeaf⟩
  · have hmissingNotB : leaf missing ∉ B := by
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
    rcases hmiddle with hk | hk
    · subst k₀
      rcases hmissingPair with hxMissing | hzMissing
      · left
        rcases hb₀Uniform with hminus | hzero
        · exact hminus.2.inserted_leafValue_eq_neg_two
            g y (middleExchangeSet g y p (-1) b₀B)
              (b₀B : Fin n) p.z p.x leaf w missing hxMissing
        · omega
      · have hwZero : w = 0 := by
          rcases hb₀Uniform with hminus | hzero
          · exact hminus.2.secondRetained_leafValue_eq_zero
              g y (middleExchangeSet g y p (-1) b₀B)
                (b₀B : Fin n) p.z p.x leaf w hd missing hzMissing
          · omega
        have hoff : ∀ b : ↥B, (b : Fin n) ∈ T →
            (b : Fin n) ∉ leafRange := by
          intro b hbT hbLeaf
          have hwMinus := hownerForces b hbT hbLeaf
          omega
        right
        right
        exact ⟨hwZero, missing, hpunctured,
          Or.inl ⟨rfl, hzMissing⟩, hoff⟩
    · subst k₀
      rcases hmissingPair with hxMissing | hzMissing
      · have hwZero : w = 0 := by
          rcases hb₀Uniform with hminus | hzero
          · omega
          · exact hzero.2.secondRetained_leafValue_eq_zero
              g y (middleExchangeSet g y p 0 b₀B)
                (b₀B : Fin n) p.x p.z leaf w hd missing hxMissing
        have hoff : ∀ b : ↥B, (b : Fin n) ∈ T →
            (b : Fin n) ∉ leafRange := by
          intro b hbT hbLeaf
          have hwMinus := hownerForces b hbT hbLeaf
          omega
        right
        right
        exact ⟨hwZero, missing, hpunctured,
          Or.inr ⟨rfl, hxMissing⟩, hoff⟩
      · left
        rcases hb₀Uniform with hminus | hzero
        · omega
        · exact hzero.2.inserted_leafValue_eq_neg_two
            g y (middleExchangeSet g y p 0 b₀B)
              (b₀B : Fin n) p.x p.z leaf w missing hzMissing

/-- Family-level lossless leaf-location classification. -/
theorem PrimitiveMiddleUniformLeafValueSubfamily.toLeafLocationClassified
    {q d : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (leaf : Fin d → Fin n)
    (hfamily : PrimitiveMiddleUniformLeafValueSubfamily g y B leaf)
    (hd : 2 ≤ d)
    (hleafIncidence :
      (∀ i, leaf i ∈ B) ∨
        ∃ missing : Fin d, ∀ i, leaf i ∈ B ↔ i ≠ missing) :
    PrimitiveMiddleLeafLocationClassifiedSubfamily g y B leaf := by
  rcases hfamily with ⟨p, S, T, k₀, w, hdata⟩
  refine ⟨p, S, T, k₀, w, hdata, ?_⟩
  exact hdata.locationOutcome
    g y B leaf p S T k₀ w hd hleafIncidence

end MinModulus
