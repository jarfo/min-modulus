/-
# Arithmetic rigidity of antipodal repair cancellation

The zero residual case has `A={0}` and `M={m}`.  Substitution into the exact
binary alternative eliminates its first lift and forces

  2^m + s = 2^d,

equivalently `s=2^d-2^m`.  Thus one external scalar can cancel at at most one
pointed leaf position.  Moreover, within a fixed repair family, cardinality
at least two rules out cancellation for every member because cancellation
already says that the common negative set is a singleton.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalRepairResidualEndpoint

namespace MinModulus

open Finset

/-- Binary subset value on a singleton is its corresponding power of two. -/
@[simp] theorem binarySubsetValue_singleton
    {d : ℕ} (i : Fin d) :
    binarySubsetValue ({i} : Finset (Fin d)) = 2 ^ i.val := by
  simp [binarySubsetValue]

/-- For positive `s`, the two-lift binary alternative on pointed singletons
is equivalent to the exact complementary-power identity. -/
theorem pointed_singleton_binaryArithmetic_iff_pow_add_eq
    {d : ℕ} (hd : 0 < d) (s : ℕ) (hs0 : 0 < s) (m : Fin d) :
    (binarySubsetValue ({⟨0, hd⟩} : Finset (Fin d)) =
        binarySubsetValue {m} + s ∨
      binarySubsetValue ({⟨0, hd⟩} : Finset (Fin d)) + (2 ^ d - 1) =
        binarySubsetValue {m} + s) ↔
      2 ^ m.val + s = 2 ^ d := by
  simp only [binarySubsetValue_singleton, pow_zero]
  have hpow : 0 < 2 ^ d := pow_pos (by norm_num) d
  constructor
  · rintro (hfirst | hsecond)
    · have hmPow : 0 < 2 ^ m.val := pow_pos (by norm_num) m.val
      omega
    · omega
  · intro heq
    right
    omega

/-- Singleton cancellation determines the external scalar explicitly. -/
theorem pointed_singleton_binaryArithmetic_forces_scalar
    {d : ℕ} (hd : 0 < d) (s : ℕ) (hs0 : 0 < s) (m : Fin d)
    (harithmetic :
      binarySubsetValue ({⟨0, hd⟩} : Finset (Fin d)) =
          binarySubsetValue {m} + s ∨
        binarySubsetValue ({⟨0, hd⟩} : Finset (Fin d)) +
            (2 ^ d - 1) = binarySubsetValue {m} + s) :
    2 ^ m.val + s = 2 ^ d ∧ s = 2 ^ d - 2 ^ m.val := by
  have heq := (pointed_singleton_binaryArithmetic_iff_pow_add_eq
    hd s hs0 m).mp harithmetic
  omega

/-- A fixed positive external scalar admits at most one singleton-cancelling
pointed leaf position. -/
theorem pointed_singleton_binaryArithmetic_index_unique
    {d : ℕ} (hd : 0 < d) (s : ℕ) (hs0 : 0 < s)
    (m₁ m₂ : Fin d)
    (h₁ :
      binarySubsetValue ({⟨0, hd⟩} : Finset (Fin d)) =
          binarySubsetValue {m₁} + s ∨
        binarySubsetValue ({⟨0, hd⟩} : Finset (Fin d)) +
            (2 ^ d - 1) = binarySubsetValue {m₁} + s)
    (h₂ :
      binarySubsetValue ({⟨0, hd⟩} : Finset (Fin d)) =
          binarySubsetValue {m₂} + s ∨
        binarySubsetValue ({⟨0, hd⟩} : Finset (Fin d)) +
            (2 ^ d - 1) = binarySubsetValue {m₂} + s) :
    m₁ = m₂ := by
  have heq₁ := (pointed_singleton_binaryArithmetic_iff_pow_add_eq
    hd s hs0 m₁).mp h₁
  have heq₂ := (pointed_singleton_binaryArithmetic_iff_pow_add_eq
    hd s hs0 m₂).mp h₂
  have hpowers : 2 ^ m₁.val = 2 ^ m₂.val := by omega
  have hvals : m₁.val = m₂.val :=
    Nat.pow_right_injective (by norm_num : 1 < (2 : ℕ)) hpowers
  exact Fin.ext hvals

/-- Substituting the singleton sets supplied by exact repair cancellation
into the endpoint's binary alternative yields its scalar law. -/
theorem binaryArithmetic_of_exactRepairCancellation
    {d : ℕ} (hd : 0 < d) (s : ℕ) (hs0 : 0 < s)
    (A M : Finset (Fin d)) (m : Fin d)
    (hA : A = {⟨0, hd⟩}) (hM : M = {m})
    (harithmetic :
      binarySubsetValue A = binarySubsetValue M + s ∨
        binarySubsetValue A + (2 ^ d - 1) = binarySubsetValue M + s) :
    2 ^ m.val + s = 2 ^ d ∧ s = 2 ^ d - 2 ^ m.val := by
  subst A
  subst M
  exact pointed_singleton_binaryArithmetic_forces_scalar
    hd s hs0 m harithmetic

/-- If a fixed repair family has at least two negative digits, no member can
lie in the exact-cancellation arm; every pointwise cancellation/residual
alternative therefore lands in its residual predicate. -/
theorem all_residual_of_two_le_card_negativeSet
    {d : ℕ} (M : Finset (Fin d)) (hM : 2 ≤ M.card)
    (Cancel Residual : Fin d → Prop)
    (houtcome : ∀ m, m ∈ M →
      (Cancel m ∧ M = {m}) ∨ Residual m) :
    ∀ m, m ∈ M → Residual m := by
  intro m hmM
  rcases houtcome m hmM with hcancel | hresidual
  · have hcardOne : M.card = 1 := by rw [hcancel.2]; simp
    omega
  · exact hresidual

/-- Family-level form of the cancellation analysis.  Either one member
cancels, in which case the common sets are the corresponding singletons and
the external scalar is forced, or every member of the fixed negative set lies
in the residual arm. -/
theorem singletonCancellation_or_all_residual
    {d : ℕ} (hd : 0 < d) (s : ℕ) (hs0 : 0 < s)
    (A M : Finset (Fin d))
    (harithmetic :
      binarySubsetValue A = binarySubsetValue M + s ∨
        binarySubsetValue A + (2 ^ d - 1) = binarySubsetValue M + s)
    (Cancel Residual : Fin d → Prop)
    (houtcome : ∀ m, m ∈ M →
      ((Cancel m ∧ A = {⟨0, hd⟩} ∧ M = {m}) ∨ Residual m)) :
    (∃ m, m ∈ M ∧ Cancel m ∧ A = {⟨0, hd⟩} ∧ M = {m} ∧
        2 ^ m.val + s = 2 ^ d ∧ s = 2 ^ d - 2 ^ m.val) ∨
      ∀ m, m ∈ M → Residual m := by
  classical
  by_cases hcancel : ∃ m, m ∈ M ∧
      (Cancel m ∧ A = {⟨0, hd⟩} ∧ M = {m})
  · left
    obtain ⟨m, hmM, hmCancel, hA, hM⟩ := hcancel
    have hscalar := binaryArithmetic_of_exactRepairCancellation
      hd s hs0 A M m hA hM harithmetic
    exact ⟨m, hmM, hmCancel, hA, hM, hscalar⟩
  · right
    intro m hmM
    rcases houtcome m hmM with hmCancel | hmResidual
    · exact False.elim (hcancel ⟨m, hmM, hmCancel⟩)
    · exact hmResidual

end MinModulus
