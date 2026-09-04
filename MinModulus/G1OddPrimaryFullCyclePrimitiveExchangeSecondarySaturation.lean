/-
# Saturating the secondary primitive residue fiber

The five-owner reservoir contains three owners with one common quotient
parameter.  Enlarge that selected triple to every deleted owner in the same
odd-kernel coset.  Primitive order sixty-four and the canonical four-value
interval force every added owner to have the same parameter and the same raw
private-row normal form.

Because the original triple is separated from the primary coset, saturation
cannot absorb a coordinate of that primary union.  The result is therefore a
complete second deleted-owner residue fiber, still disjoint from and
separated from the primary union.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeSecondaryFiber

namespace MinModulus

open Finset

variable {n : ℕ}

/-- The complete secondary deleted-owner residue fiber.  The named base
owner makes its exact coset-membership equation available downstream. -/
def PrimitiveSaturatedSecondaryResidueFiber
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B U : Finset (Fin n))
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
    ∀ b ∈ T, ∀ c ∈ U,
      g b - g c ∉ AddSubgroup.zmultiples y

/-- Saturate a secondary residue triple to its complete deleted-owner coset.
No member of the primary union can enter the saturation, and every new owner
inherits the same canonical private-row parameter by primitive quotient
uniqueness. -/
theorem PrimitiveSecondaryResidueFiber.toSaturated
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
    (hseparated : ∀ b ∈ B \ U, ∀ c ∈ U,
      g b - g c ∉ AddSubgroup.zmultiples y)
    (hsecondary : PrimitiveSecondaryResidueFiber g y B U p k₀) :
    PrimitiveSaturatedSecondaryResidueFiber g y B U p k₀ := by
  classical
  rcases hsecondary with
    ⟨T₀, k₁, hT₀card, hT₀sub, hk₁Mem, hk₁Ne, hrows₀, hcoset₀⟩
  have hT₀nonempty : T₀.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨t, htT₀⟩ := hT₀nonempty
  have htOutside : t ∈ B \ U := hT₀sub htT₀
  have htB : t ∈ B := (Finset.mem_sdiff.mp htOutside).1
  let T : Finset (Fin n) :=
    B.filter (fun b ↦ g b - g t ∈ AddSubgroup.zmultiples y)
  have hT₀subT : T₀ ⊆ T := by
    intro b hbT₀
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_sdiff.mp (hT₀sub hbT₀)).1,
        hcoset₀ b hbT₀ t htT₀⟩
  have hTcard : 3 ≤ T.card :=
    hT₀card.trans (Finset.card_le_card hT₀subT)
  have htT : t ∈ T := hT₀subT htT₀
  have hTsub : T ⊆ B \ U := by
    intro b hbT
    have hbFilter := Finset.mem_filter.mp hbT
    refine Finset.mem_sdiff.mpr ⟨hbFilter.1, ?_⟩
    intro hbU
    have hnot := hseparated t htOutside b hbU
    apply hnot
    have hneg :=
      (AddSubgroup.zmultiples y).neg_mem hbFilter.2
    convert hneg using 1
    module
  have htRow := hrows₀ ⟨t, htB⟩ htT₀
  have hrows : ∀ b : ↥B, (b : Fin n) ∈ T →
      (p.coeff b (b : Fin n) = -1 ∨
        p.coeff b (b : Fin n) = 1) ∧
      p.weight b = 2 * k₁ ∧
      g (b : Fin n) - g p.z + k₁ • (g p.x - g p.z) ∈
        AddSubgroup.zmultiples y ∧
      (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
          (g (b : Fin n) - g p.z) =
        -(k₁ •
          (QuotientAddGroup.mk' (AddSubgroup.zmultiples y))
            (g p.x - g p.z)) := by
    intro b hbT
    have hparallel := (Finset.mem_filter.mp hbT).2
    obtain ⟨howner, k, hkMem, hweight, hcorrected, hquotient⟩ :=
      p.primitive_unitRowNormalForm
        g y B hyq hfullOdd hprimitive b
    have hkEq : k = k₁ :=
      primitive_fourResidueParameter_eq_of_pairDifference_mem
        g y p.x p.z (b : Fin n) t hprimitive k k₁ hkMem hk₁Mem
          hquotient htRow.2.2.2 hparallel
    refine ⟨howner, ?_, ?_, ?_⟩
    · simpa only [hkEq] using hweight
    · simpa only [hkEq] using hcorrected
    · simpa only [hkEq] using hquotient
  refine ⟨T, k₁, t, hTcard, hTsub, htT, hk₁Mem, hk₁Ne,
    hrows, ?_, ?_⟩
  · intro b
    simp only [T, Finset.mem_filter, b.property, true_and]
  · intro b hbT c hcU
    exact hseparated b (hTsub hbT) c hcU

end MinModulus
