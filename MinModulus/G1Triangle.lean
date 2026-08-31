/-
# Three-witness closure for the G1 common-touch problem

This module isolates reusable triangle-omission arguments from the core
two-adic descent machinery.  Three witnesses at a nonzero involution add to a
witness whenever their coefficientwise sum remains at least `-1`; a unique
omission in that sum then closes the common-touch branch of G1.
-/
import MinModulus.Descent

namespace MinModulus

open Finset

variable {n : ℕ} {G : Type*} [AddCommGroup G]

/-- Three witnesses at a nonzero involution are closed under addition whenever
their coordinatewise sum stays above the witness floor `-1`.  Their total
coefficient sum is still zero, and their values add to `3h = h`. -/
theorem witness_three_sum (g : Fin n → G) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    {c₁ c₂ c₃ : Fin n → ℤ} (hc₁ : Witness g h c₁)
    (hc₂ : Witness g h c₂) (hc₃ : Witness g h c₃)
    (hfloor : ∀ i, -1 ≤ (c₁ + c₂ + c₃) i) :
    Witness g h (c₁ + c₂ + c₃) := by
  refine ⟨three_witnesses_sum_ne_zero g hh hne hc₁ hc₂ hc₃, hfloor, ?_, ?_⟩
  · simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
      hc₁.2.2.1, hc₂.2.2.1, hc₃.2.2.1, add_zero]
    norm_num
  · have hterm : ∀ i, (c₁ + c₂ + c₃) i • g i
        = c₁ i • g i + c₂ i • g i + c₃ i • g i := by
      intro i
      simp only [Pi.add_apply, add_smul]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_add_distrib,
      Finset.sum_add_distrib, hc₁.2.2.2, hc₂.2.2.2, hc₃.2.2.2, hh, zero_add]

/-- If the admissible sum of three witnesses has a unique omission, that
omitted coordinate is touched by every witness.  This packages the
three-witness closure directly in the common-touch form needed by G1. -/
theorem common_touched_of_three_sum_unique_omission
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    {c₁ c₂ c₃ : Fin n → ℤ} (hc₁ : Witness g h c₁)
    (hc₂ : Witness g h c₂) (hc₃ : Witness g h c₃)
    (hfloor : ∀ i, -1 ≤ (c₁ + c₂ + c₃) i)
    (b : Fin n) (hb : (c₁ + c₂ + c₃) b = -1)
    (huniq : ∀ i, (c₁ + c₂ + c₃) i = -1 → i = b) :
    ∀ c : Fin n → ℤ, Witness g h c → c b ≠ 0 := by
  exact common_touched_of_unique_omission g hg hh
    (witness_three_sum g hh hne hc₁ hc₂ hc₃ hfloor) b hb huniq

/-- **Triangle closure, one light opposite.**  Suppose three witnesses have
exact omission pairs `{a,b}`, `{b,d}`, and `{d,a}`.  If the coefficient
opposite `{a,b}` is exactly `1`, while the other two opposite coefficients
are at least `2`, then their sum is a witness whose unique omission is `d`.
Consequently every witness touches `d`, proving the G1 common-touch conclusion
for this entire triangle coefficient pattern (and its permutations). -/
theorem common_touched_of_triangle_one_light_opposite
    (g : Fin n → G) (hg : ValidTuple g) {h : G}
    (hh : h + h = 0) (hne : h ≠ 0)
    {cAB cBD cDA : Fin n → ℤ} (hcAB : Witness g h cAB)
    (hcBD : Witness g h cBD) (hcDA : Witness g h cDA)
    (a b d : Fin n)
    (hAB : ∀ i, cAB i = -1 ↔ i = a ∨ i = b)
    (hBD : ∀ i, cBD i = -1 ↔ i = b ∨ i = d)
    (hDA : ∀ i, cDA i = -1 ↔ i = d ∨ i = a)
    (hlight : cAB d = 1) (hheavyA : 2 ≤ cBD a)
    (hheavyB : 2 ≤ cDA b) :
    ∀ c : Fin n → ℤ, Witness g h c → c d ≠ 0 := by
  have hABa : cAB a = -1 := (hAB a).2 (Or.inl rfl)
  have hABb : cAB b = -1 := (hAB b).2 (Or.inr rfl)
  have hBDb : cBD b = -1 := (hBD b).2 (Or.inl rfl)
  have hBDd : cBD d = -1 := (hBD d).2 (Or.inr rfl)
  have hDAd : cDA d = -1 := (hDA d).2 (Or.inl rfl)
  have hDAa : cDA a = -1 := (hDA a).2 (Or.inr rfl)
  have hfloor : ∀ i, -1 ≤ (cAB + cBD + cDA) i := by
    intro i
    by_cases hid : i = d
    · subst i
      simp only [Pi.add_apply]
      omega
    by_cases hia : i = a
    · subst i
      simp only [Pi.add_apply]
      omega
    by_cases hib : i = b
    · subst i
      simp only [Pi.add_apply]
      omega
    have hABi : cAB i ≠ -1 := by
      intro hi
      rcases (hAB i).1 hi with rfl | rfl <;> contradiction
    have hBDi : cBD i ≠ -1 := by
      intro hi
      rcases (hBD i).1 hi with rfl | rfl <;> contradiction
    have hDAi : cDA i ≠ -1 := by
      intro hi
      rcases (hDA i).1 hi with rfl | rfl <;> contradiction
    have hABnonneg : 0 ≤ cAB i := by have := hcAB.2.1 i; omega
    have hBDnonneg : 0 ≤ cBD i := by have := hcBD.2.1 i; omega
    have hDAnonneg : 0 ≤ cDA i := by have := hcDA.2.1 i; omega
    simp only [Pi.add_apply]
    omega
  have hd : (cAB + cBD + cDA) d = -1 := by
    simp only [Pi.add_apply]
    omega
  have huniq : ∀ i, (cAB + cBD + cDA) i = -1 → i = d := by
    intro i hi
    by_contra hid
    by_cases hia : i = a
    · subst i
      simp only [Pi.add_apply] at hi
      omega
    by_cases hib : i = b
    · subst i
      simp only [Pi.add_apply] at hi
      omega
    have hABi : cAB i ≠ -1 := by
      intro hci
      rcases (hAB i).1 hci with rfl | rfl <;> contradiction
    have hBDi : cBD i ≠ -1 := by
      intro hci
      rcases (hBD i).1 hci with rfl | rfl <;> contradiction
    have hDAi : cDA i ≠ -1 := by
      intro hci
      rcases (hDA i).1 hci with rfl | rfl <;> contradiction
    have hABnonneg : 0 ≤ cAB i := by have := hcAB.2.1 i; omega
    have hBDnonneg : 0 ≤ cBD i := by have := hcBD.2.1 i; omega
    have hDAnonneg : 0 ≤ cDA i := by have := hcDA.2.1 i; omega
    simp only [Pi.add_apply] at hi
    omega
  exact common_touched_of_three_sum_unique_omission g hg hh hne
    hcAB hcBD hcDA hfloor d hd huniq

end MinModulus
