import MinModulus.SILiftReduce

/-!
# Sheet parity of an SI rival

A rival of the SI parent that omits the extra is a coin family `k` on
exponents `0 .. m-1` with `dsum m k = m + 1`.  Its sheet contribution is
governed by `E = {i : k i even}`, because the coefficient `k i - 1` is odd
exactly when `k i` is even.

`si_even_card_odd` records the governing fact: `E` always has ODD
cardinality.  Hence a child lifted by a CONSTANT sheet bit has sheet
parity equal to that constant for every rival — which is why the
constant-bit lifts admit exactly one surviving extra, and why only a
non-constant lift can reach both parities.
-/

namespace MinModulus

open Finset

/-- **The even-position count is odd.**  Any coin family on `m` exponents
carrying `m + 1` coins has an odd number of even multiplicities. -/
theorem si_even_card_odd (m : ℕ) (k : ℕ → ℕ) (hd : dsum m k = m + 1) :
    ((range m).filter (fun i => k i % 2 = 0)).card % 2 = 1 := by
  classical
  have hsplit : ((range m).filter (fun i => k i % 2 = 0)).card
      + ((range m).filter (fun i => k i % 2 = 1)).card = m := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := range m) (p := fun i => k i % 2 = 0)
    rw [Finset.card_range] at h
    have hneg : ((range m).filter (fun i => ¬ (k i % 2 = 0))).card
        = ((range m).filter (fun i => k i % 2 = 1)).card := by
      refine congrArg Finset.card (Finset.filter_congr ?_)
      intro i _
      constructor <;> (intro hx; omega)
    rw [← hneg]
    exact h
  have hmod : dsum m k % 2
      = ((range m).filter (fun i => k i % 2 = 1)).card % 2 := by
    unfold dsum
    rw [Finset.sum_nat_mod, Finset.card_filter]
    congr 1
    refine Finset.sum_congr rfl ?_
    intro i _
    split <;> omega
  rw [hd] at hmod
  omega

/-- For a constant sheet bit, the sheet contribution of every rival has
the parity of that constant. -/
theorem si_sheet_parity_const (m : ℕ) (k : ℕ → ℕ) (hd : dsum m k = m + 1)
    (β : ℕ) :
    (∑ _i ∈ (range m).filter (fun i => k i % 2 = 0), β) % 2 = β % 2 := by
  classical
  rw [Finset.sum_const, smul_eq_mul]
  have h := si_even_card_odd m k hd
  obtain ⟨c, hc⟩ : ∃ c, ((range m).filter (fun i => k i % 2 = 0)).card
      = 2 * c + 1 :=
    ⟨((range m).filter (fun i => k i % 2 = 0)).card / 2, by omega⟩
  rw [hc]
  have hexp : (2 * c + 1) * β = 2 * (c * β) + β := by ring
  rw [hexp]
  omega

end MinModulus
