/-
# Exhaustive three-residue partition in the windowed primitive middle arm

After the primary and secondary deleted-owner fibers have been saturated,
every remaining deleted owner has one of the two unused canonical quotient
parameters.  The global unit window excludes one outer parameter.  Hence all
remaining owners share the other parameter and form one final complete
odd-kernel residue fiber.

This replaces the potentially open-ended secondary-fiber iteration by an
exhaustive partition into at most three complete residue classes.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeWindowedCritical

namespace MinModulus

open Finset

variable {n : ℕ}

/-- Once a middle parameter, a distinct secondary parameter, and one outer
parameter have been excluded from the canonical four-value interval, the
remaining parameter is unique. -/
theorem primitive_threeWindow_remainingParameter_eq
    (k₀ k₁ kb kc : ℤ)
    (hmiddle : k₀ = -1 ∨ k₀ = 0)
    (hk₁Mem : k₁ ∈ ({-2, -1, 0, 1} : Finset ℤ))
    (hk₁Ne : k₁ ≠ k₀)
    (hkbMem : kb ∈ ({-2, -1, 0, 1} : Finset ℤ))
    (hkcMem : kc ∈ ({-2, -1, 0, 1} : Finset ℤ))
    (hkbNe₀ : kb ≠ k₀) (hkcNe₀ : kc ≠ k₀)
    (hkbNe₁ : kb ≠ k₁) (hkcNe₁ : kc ≠ k₁)
    (habsent :
      (k₁ ≠ -2 ∧ kb ≠ -2 ∧ kc ≠ -2) ∨
        (k₁ ≠ 1 ∧ kb ≠ 1 ∧ kc ≠ 1)) :
    kb = kc := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk₁Mem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkbMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hkcMem
  rcases hmiddle with hk₀ | hk₀ <;>
    rcases hk₁Mem with hk₁ | hk₁ | hk₁ | hk₁ <;>
    rcases hkbMem with hkb | hkb | hkb | hkb <;>
    rcases hkcMem with hkc | hkc | hkc | hkc <;>
    rcases habsent with ⟨hk₁Absent, hkbAbsent, hkcAbsent⟩ |
      ⟨hk₁Absent, hkbAbsent, hkcAbsent⟩ <;> simp_all

/-- Relative to two already saturated fibers, the rest of the transversal is
either empty or one final complete canonical residue fiber. -/
def PrimitiveFinalResiduePartition
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B S T : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ k₁ : ℤ) : Prop :=
  ∃ F : Finset (Fin n),
    B = (S ∪ T) ∪ F ∧
    (F = ∅ ∨
      ∃ k₂ : ℤ, ∃ f : Fin n,
        f ∈ F ∧
        k₂ ∈ ({-2, -1, 0, 1} : Finset ℤ) ∧
        k₂ ≠ k₀ ∧ k₂ ≠ k₁ ∧
        (∀ b : ↥B, (b : Fin n) ∈ F →
          (p.coeff b (b : Fin n) = -1 ∨
            p.coeff b (b : Fin n) = 1) ∧
          p.weight b = 2 * k₂ ∧
          g (b : Fin n) - g p.z + k₂ • (g p.x - g p.z) ∈
            AddSubgroup.zmultiples y ∧
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g (b : Fin n) - g p.z) =
            -(k₂ •
              (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
                (g p.x - g p.z))) ∧
        ∀ b : ↥B,
          ((b : Fin n) ∈ F ↔
            g (b : Fin n) - g f ∈ AddSubgroup.zmultiples y))

/-- The saturated secondary capacity package, enriched by the exhaustive
at-most-three-class partition of the whole deleted transversal. -/
def PrimitiveThreeResidueCapacityPartition
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B U S : Finset (Fin n))
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) : Prop :=
  ∃ T : Finset (Fin n), ∃ k₁ : ℤ, ∃ t : Fin n,
    3 ≤ T.card ∧ T ⊆ B \ U ∧ t ∈ T ∧
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
    (∀ b : ↥B,
      ((b : Fin n) ∈ T ↔
        g (b : Fin n) - g t ∈ AddSubgroup.zmultiples y)) ∧
    (∀ b ∈ T, ∀ c ∈ U,
      g b - g c ∉ AddSubgroup.zmultiples y) ∧
    (∀ i j : ℕ, U.card.choose i * T.card.choose j ≤ q) ∧
    PrimitiveFinalResiduePartition g y B S T p k₀ k₁

/-- Exact saturation of two distinct canonical residue fibers, together with
the global three-residue window, leaves at most one complete residual fiber.
All three classes use one unchanged canonical private presentation. -/
theorem PrimitiveSaturatedSecondaryResidueCapacity.toThreeResiduePartition
    {q : ℕ} [NeZero (2 ^ 6 * q)]
    (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B U S : Finset (Fin n))
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
    (hSsub : S ⊆ B)
    (hSrows : ∀ b : ↥B, (b : Fin n) ∈ S →
      p.weight b = 2 * k₀)
    (hScomplete : ∀ b : ↥B,
      ((b : Fin n) ∈ S ↔
        g (b : Fin n) - g (primitiveMiddleInsertedCoordinate p k₀) ∈
          AddSubgroup.zmultiples y))
    (hcapacity :
      PrimitiveSaturatedSecondaryResidueCapacity g y B U p k₀) :
    PrimitiveThreeResidueCapacityPartition g y B U S p k₀ := by
  classical
  rcases hcapacity with
    ⟨T, k₁, t, hTcard, hTsub, htT, hk₁Mem, hk₁Ne, hTrows,
      hTcomplete, hTseparated, hcap⟩
  let rawK : ↥B → ℤ := fun b ↦
    Classical.choose
      (p.primitive_unitRowNormalForm
        g y B hyq hfullOdd hprimitive b).2
  have hownerSpec : ∀ b : ↥B,
      p.coeff b (b : Fin n) = -1 ∨
        p.coeff b (b : Fin n) = 1 := by
    intro b
    exact (p.primitive_unitRowNormalForm
      g y B hyq hfullOdd hprimitive b).1
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
    exact Classical.choose_spec
      (p.primitive_unitRowNormalForm
        g y B hyq hfullOdd hprimitive b).2
  have hSraw : ∀ b : ↥B, (b : Fin n) ∈ S → rawK b = k₀ := by
    intro b hbS
    have hweightS := hSrows b hbS
    have hweightRaw := (hkSpec b).2.1
    omega
  have hTraw : ∀ b : ↥B, (b : Fin n) ∈ T → rawK b = k₁ := by
    intro b hbT
    have hweightT := (hTrows b hbT).2.1
    have hweightRaw := (hkSpec b).2.1
    omega
  let F : Finset (Fin n) := B \ (S ∪ T)
  have hpartition : B = (S ∪ T) ∪ F := by
    ext b
    simp only [F, Finset.mem_union, Finset.mem_sdiff]
    constructor
    · intro hbB
      by_cases hbST : b ∈ S ∨ b ∈ T
      · exact Or.inl hbST
      · exact Or.inr ⟨hbB, hbST⟩
    · intro hb
      rcases hb with hbST | hbF
      · rcases hbST with hbS | hbT
        · exact hSsub hbS
        · exact (Finset.mem_sdiff.mp (hTsub hbT)).1
      · exact hbF.1
  by_cases hFempty : F = ∅
  · refine ⟨T, k₁, t, hTcard, hTsub, htT, hk₁Mem, hk₁Ne,
      hTrows, hTcomplete, hTseparated, hcap, F, hpartition, Or.inl hFempty⟩
  · have hFnonempty : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hFempty
    obtain ⟨f, hfF⟩ := hFnonempty
    have hfB : f ∈ B := (Finset.mem_sdiff.mp hfF).1
    let fB : ↥B := ⟨f, hfB⟩
    let k₂ : ℤ := rawK fB
    have hnotS : ∀ b : ↥B, (b : Fin n) ∈ F → (b : Fin n) ∉ S := by
      intro b hbF hbS
      exact (Finset.mem_sdiff.mp hbF).2 (Finset.mem_union_left T hbS)
    have hnotT : ∀ b : ↥B, (b : Fin n) ∈ F → (b : Fin n) ∉ T := by
      intro b hbF hbT
      exact (Finset.mem_sdiff.mp hbF).2 (Finset.mem_union_right S hbT)
    have hrawNe₀ : ∀ b : ↥B, (b : Fin n) ∈ F → rawK b ≠ k₀ := by
      intro b hbF hkEq
      apply hnotS b hbF
      apply (hScomplete b).2
      rcases hmiddle with hk₀ | hk₀
      · have hcorrected := (hkSpec b).2.2.1
        simp only [primitiveMiddleInsertedCoordinate, hk₀, if_true]
        rw [hkEq, hk₀] at hcorrected
        convert hcorrected using 1
        module
      · have hk₀Ne : k₀ ≠ -1 := by omega
        have hcorrected := (hkSpec b).2.2.1
        simp only [primitiveMiddleInsertedCoordinate, hk₀Ne, if_false]
        rw [hkEq, hk₀] at hcorrected
        simpa using hcorrected
    have hrawNe₁ : ∀ b : ↥B, (b : Fin n) ∈ F → rawK b ≠ k₁ := by
      intro b hbF hkEq
      apply hnotT b hbF
      apply (hTcomplete b).2
      have htOutside := hTsub htT
      let tB : ↥B := ⟨t, (Finset.mem_sdiff.mp htOutside).1⟩
      have hbCorrected := (hkSpec b).2.2.1
      have htCorrected := (hTrows tB htT).2.2.1
      rw [hkEq] at hbCorrected
      have hsub :=
        (AddSubgroup.zmultiples y).sub_mem hbCorrected htCorrected
      convert hsub using 1
      module
    have hremainingEq : ∀ b : ↥B, (b : Fin n) ∈ F → rawK b = k₂ := by
      intro b hbF
      apply primitive_threeWindow_remainingParameter_eq
        k₀ k₁ (rawK b) k₂ hmiddle hk₁Mem hk₁Ne
          (hkSpec b).1 (hkSpec fB).1
          (hrawNe₀ b hbF) (hrawNe₀ fB hfF)
          (hrawNe₁ b hbF) (hrawNe₁ fB hfF)
      rcases hwindow with hnoMinus | hnoPlus
      · left
        refine ⟨?_, ?_, ?_⟩
        · intro hk
          have htOutside := hTsub htT
          let tB : ↥B := ⟨t, (Finset.mem_sdiff.mp htOutside).1⟩
          have hw := (hTrows tB htT).2.1
          rw [hk] at hw
          exact hnoMinus tB (by omega)
        · intro hk
          have hw := (hkSpec b).2.1
          rw [hk] at hw
          exact hnoMinus b (by omega)
        · intro hk
          have hw := (hkSpec fB).2.1
          change rawK fB = -2 at hk
          rw [hk] at hw
          exact hnoMinus fB (by omega)
      · right
        refine ⟨?_, ?_, ?_⟩
        · intro hk
          have htOutside := hTsub htT
          let tB : ↥B := ⟨t, (Finset.mem_sdiff.mp htOutside).1⟩
          have hw := (hTrows tB htT).2.1
          rw [hk] at hw
          exact hnoPlus tB (by omega)
        · intro hk
          have hw := (hkSpec b).2.1
          rw [hk] at hw
          exact hnoPlus b (by omega)
        · intro hk
          have hw := (hkSpec fB).2.1
          change rawK fB = 1 at hk
          rw [hk] at hw
          exact hnoPlus fB (by omega)
    have hFrows : ∀ b : ↥B, (b : Fin n) ∈ F →
        (p.coeff b (b : Fin n) = -1 ∨
          p.coeff b (b : Fin n) = 1) ∧
        p.weight b = 2 * k₂ ∧
        g (b : Fin n) - g p.z + k₂ • (g p.x - g p.z) ∈
          AddSubgroup.zmultiples y ∧
        (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g (b : Fin n) - g p.z) =
          -(k₂ •
            (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
              (g p.x - g p.z)) := by
      intro b hbF
      have hk := hremainingEq b hbF
      exact ⟨hownerSpec b, by simpa only [hk] using (hkSpec b).2.1,
        by simpa only [hk] using (hkSpec b).2.2.1,
        by simpa only [hk] using (hkSpec b).2.2.2⟩
    have hFcomplete : ∀ b : ↥B,
        ((b : Fin n) ∈ F ↔
          g (b : Fin n) - g f ∈ AddSubgroup.zmultiples y) := by
      intro b
      constructor
      · intro hbF
        have hbCorrected := (hFrows b hbF).2.2.1
        have hfCorrected := (hFrows fB hfF).2.2.1
        have hsub :=
          (AddSubgroup.zmultiples y).sub_mem hbCorrected hfCorrected
        convert hsub using 1
        module
      · intro hparallel
        have hkEq :=
          primitive_fourResidueParameter_eq_of_pairDifference_mem
            g y p.x p.z (b : Fin n) f hprimitive (rawK b) k₂
              (hkSpec b).1 (hkSpec fB).1 (hkSpec b).2.2.2
              (hkSpec fB).2.2.2 hparallel
        apply Finset.mem_sdiff.mpr
        refine ⟨b.property, ?_⟩
        intro hbST
        rcases Finset.mem_union.mp hbST with hbS | hbT
        · apply hrawNe₀ fB hfF
          exact hkEq.symm.trans (hSraw b hbS)
        · apply hrawNe₁ fB hfF
          exact hkEq.symm.trans (hTraw b hbT)
    refine ⟨T, k₁, t, hTcard, hTsub, htT, hk₁Mem, hk₁Ne,
      hTrows, hTcomplete, hTseparated, hcap, F, hpartition, Or.inr ?_⟩
    exact ⟨k₂, f, hfF, (hkSpec fB).1, hrawNe₀ fB hfF,
      hrawNe₁ fB hfF, hFrows, hFcomplete⟩

end MinModulus
