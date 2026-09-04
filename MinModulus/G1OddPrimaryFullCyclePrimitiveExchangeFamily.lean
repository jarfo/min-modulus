/-
# The simultaneous family of primitive middle exchanges

The middle residue geometry gives one exchange alternative for every owner
in a set of cardinality at least sixteen.  Here the pointwise alternatives
are assembled into the global dichotomy needed by the descent: either one
exchange already retains at least three quotient coordinates, or every
literal owner exchange is a primitive exact-two transversal.

The exchange map is injective.  Hence the all-exact arm contains at least
sixteen genuinely distinct minimal transversals, not sixteen presentations of
one unnamed object.  This is the correct input for restoring leaf incidence.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveResidueGeometry

namespace MinModulus

open Finset

variable {n : ℕ}

/-- Replacing different members of a finite set by one fixed external point
produces different finsets. -/
theorem insert_erase_owner_injective
    {B : Finset (Fin n)} {r : Fin n} (hr : r ∉ B) :
    Function.Injective (fun b : ↥B ↦ insert r (B.erase (b : Fin n))) := by
  classical
  intro b c hsets
  apply Subtype.ext
  by_contra hbc
  have hcMem : (c : Fin n) ∈ insert r (B.erase (b : Fin n)) := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_erase.mpr ⟨fun hcb ↦ hbc hcb.symm,
      c.property⟩
  change insert r (B.erase (b : Fin n)) =
    insert r (B.erase (c : Fin n)) at hsets
  rw [hsets] at hcMem
  have hcNeR : (c : Fin n) ≠ r := by
    intro hcr
    exact hr (hcr ▸ c.property)
  simp only [Finset.mem_insert, Finset.mem_erase, hcNeR, false_or,
    ne_eq, not_true_eq_false, false_and] at hcMem

/-- The literal exchange selected by a middle residue.  The only admissible
parameters are `-1` and `0`; the fallback branch is therefore the `0` branch.
-/
def middleExchangeSet {q : ℕ}
    (g : Fin n → ZMod (2 ^ 6 * q)) (y : ZMod (2 ^ 6 * q))
    {B : Finset (Fin n)}
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) (b : ↥B) : Finset (Fin n) :=
  if k₀ = -1 then insert p.x (B.erase (b : Fin n))
  else insert p.z (B.erase (b : Fin n))

/-- On the middle parameter range, the literal exchange set is injective in
its deleted owner. -/
theorem middleExchangeSet_injective
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) {B : Finset (Fin n)}
    (p : TwoRetainedCanonicalPrivatePresentation g y B)
    (k₀ : ℤ) (hmiddle : k₀ = -1 ∨ k₀ = 0) :
    Function.Injective (middleExchangeSet g y p k₀) := by
  rcases hmiddle with hk | hk
  · subst k₀
    intro b c hsets
    apply insert_erase_owner_injective p.x_not_mem
    simpa only [middleExchangeSet, if_true] using hsets
  · subst k₀
    have hzero : (0 : ℤ) ≠ -1 := by omega
    intro b c hsets
    apply insert_erase_owner_injective p.z_not_mem
    simpa only [middleExchangeSet, hzero, if_false] using hsets

/-- The simultaneous survivor after every member of the large middle class
has been exchanged and no exchange enters the three-retained C2 arm. -/
def PrimitiveMiddleAllExactExchangeFamily
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n)) : Prop :=
  ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
    ∃ S : Finset (Fin n), ∃ k₀ : ℤ,
      16 ≤ S.card ∧ S ⊆ B ∧ (k₀ = -1 ∨ k₀ = 0) ∧
      ∀ b : ↥B, (b : Fin n) ∈ S →
        PrimitiveTwoRetainedSixthStratumRows g y
          (middleExchangeSet g y p k₀ b)

/-- Assemble all pointwise middle exchanges.  Either one strict minimization
enters C2, or all at-least-sixteen explicit exchanges survive as primitive
exact-two states. -/
theorem PrimitiveMiddleExchangeFamily.three_or_allExactExchangeFamily
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
      PrimitiveMiddleAllExactExchangeFamily g y B := by
  classical
  obtain ⟨p, S, k₀, hScard, hSsub, hmiddle, houtcomes⟩ :=
    hfamily.exchange_each_fixed_to_primitive_or_three
      g hg hh hne hunique hno y hyq hfullOdd B hmin hretained hminimal
  by_cases hthree :
      ∃ b : ↥B, (b : Fin n) ∈ S ∧
        ∃ B₀ : Finset (Fin n),
          MinimalCyclicKernelSupportTransversal g y B₀ ∧
            3 ≤ n - B₀.card
  · left
    obtain ⟨b, hbS, B₀, hB₀⟩ := hthree
    exact ⟨B₀, hB₀⟩
  · right
    refine ⟨p, S, k₀, hScard, hSsub, hmiddle, ?_⟩
    intro b hbS
    rcases houtcomes b hbS with hB₀ | hminus | hzero
    · exact (hthree ⟨b, hbS, hB₀⟩).elim
    · have hk : k₀ = -1 := hminus.1
      simpa only [middleExchangeSet, hk, if_true] using hminus.2
    · have hk : k₀ = 0 := hzero.1
      have hzeroNe : k₀ ≠ -1 := by omega
      simpa only [middleExchangeSet, hzeroNe, if_false] using hzero.2

/-- The all-exact family contains pairwise distinct literal minimal
transversals, indexed injectively by the selected owners. -/
theorem PrimitiveMiddleAllExactExchangeFamily.exchangeSet_injective
    {q : ℕ} (g : Fin n → ZMod (2 ^ 6 * q))
    (y : ZMod (2 ^ 6 * q)) (B : Finset (Fin n))
    (hfamily : PrimitiveMiddleAllExactExchangeFamily g y B) :
    ∃ p : TwoRetainedCanonicalPrivatePresentation g y B,
      ∃ S : Finset (Fin n), ∃ k₀ : ℤ,
        16 ≤ S.card ∧ S ⊆ B ∧
        Function.Injective (middleExchangeSet g y p k₀) ∧
        ∀ b : ↥B, (b : Fin n) ∈ S →
          PrimitiveTwoRetainedSixthStratumRows g y
            (middleExchangeSet g y p k₀ b) := by
  rcases hfamily with ⟨p, S, k₀, hScard, hSsub, hmiddle, hstates⟩
  exact ⟨p, S, k₀, hScard, hSsub,
    middleExchangeSet_injective g y p k₀ hmiddle, hstates⟩

end MinModulus
