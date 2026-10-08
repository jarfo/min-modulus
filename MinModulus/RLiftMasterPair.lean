import MinModulus.RLiftBits
import MinModulus.RLiftS2
import MinModulus.RLiftPowerChain
import MinModulus.RLiftRival
import MinModulus.RLiftGridTable

/-!
# Master family: the carry-flip pair contradiction

Two rivals with the same odd-coefficient support whose integer values
differ by exactly `2M` pin the same sheet-bit sum to opposite targets.
This is the master family's closing mechanism: the base digit rival and
its `z₁`/`z₂` shift partner.
-/

namespace MinModulus

open Finset

/-- Casting an integer multiple of `2M` into `ZMod 4M` gives `0` or the
sheet. -/
lemma intCast_two_mul_M_mul (L : ℕ) (G : ℤ) :
    ((2 * (2 ^ (L + 1) - 1) * G : ℤ) : ZMod (2 ^ (L + 3) - 4)) = 0 ∨
    ((2 * (2 ^ (L + 1) - 1) * G : ℤ) : ZMod (2 ^ (L + 3) - 4)) = sheet L := by
  have hmod : ((2 ^ (L + 3) - 4 : ℕ) : ℤ) = 4 * (2 ^ (L + 1) - 1) := by
    have h := rlift_modulus L
    have h1 : (1:ℕ) ≤ 2 ^ (L + 1) := Nat.one_le_pow _ _ (by norm_num)
    push_cast [h, Nat.cast_sub h1]
    ring
  rcases Int.even_or_odd G with ⟨t, ht⟩ | ⟨t, ht⟩
  · left
    have : (2 * (2 ^ (L + 1) - 1) * G : ℤ)
        = t * ((2 ^ (L + 3) - 4 : ℕ) : ℤ) := by
      rw [hmod, ht]
      ring
    rw [this, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero]
  · right
    have h1 : (1:ℕ) ≤ 2 ^ (L + 1) := Nat.one_le_pow _ _ (by norm_num)
    have : (2 * (2 ^ (L + 1) - 1) * G : ℤ)
        = t * ((2 ^ (L + 3) - 4 : ℕ) : ℤ)
          + ((2 * (2 ^ (L + 1) - 1) : ℕ) : ℤ) := by
      rw [hmod, ht]
      push_cast [Nat.cast_sub h1]
      ring
    rw [this, Int.cast_add, Int.cast_mul, Int.cast_natCast, Int.cast_natCast,
        ZMod.natCast_self, mul_zero, zero_add]
    rfl

/-- Casting `±2M` gives the sheet. -/
lemma intCast_two_mul_M (L : ℕ) :
    ((2 * (2 ^ (L + 1) - 1) : ℤ) : ZMod (2 ^ (L + 3) - 4)) = sheet L := by
  have h := intCast_two_mul_M_mul L 1
  rcases h with h | h
  · exfalso
    rw [mul_one] at h
    have h1 : (1:ℕ) ≤ 2 ^ (L + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hcast : ((2 * (2 ^ (L + 1) - 1) : ℤ)) = ((2 * (2 ^ (L + 1) - 1) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h1]
      ring
    rw [hcast, Int.cast_natCast] at h
    exact sheet_ne_zero L (h ▸ rfl)
  · rw [mul_one] at h
    exact h

lemma intCast_neg_two_mul_M (L : ℕ) :
    ((-(2 * (2 ^ (L + 1) - 1)) : ℤ) : ZMod (2 ^ (L + 3) - 4)) = sheet L := by
  rw [Int.cast_neg, intCast_two_mul_M]
  have h2 := two_nsmul_sheet L
  rw [two_nsmul] at h2
  exact neg_eq_of_add_eq_zero_right h2

/-- **The pair contradiction.**  Two admissible rivals with equal
odd-coefficient support, both using the extra, whose integer values
differ by `±2M` with the base value a multiple of `2M`, cannot both be
avoided: no valid tuple exists. -/
lemma master_pair_contra {L : ℕ}
    {g β : Fin (L + 3) → ZMod (2 ^ (L + 3) - 4)} {r : Fin (L + 3) → ℕ}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet L)
    (hg : ∀ i, g i = ((r i : ℕ) : ZMod (2 ^ (L + 3) - 4)) + β i)
    (hv : ValidTuple g)
    (c c' : Fin (L + 3) → ℤ)
    (hfloor : ∀ i, -1 ≤ c i) (hfloor' : ∀ i, -1 ≤ c' i)
    (hsum : ∑ i, c i = 0) (hsum' : ∑ i, c' i = 0)
    {j₀ : Fin (L + 3)} (hwit : c j₀ ≠ 0) (hwit' : c' j₀ ≠ 0)
    (hpar : ∀ i, Odd (c i) ↔ Odd (c' i))
    (hV : ∃ G : ℤ, ∑ i, c i * (r i : ℤ) = 2 * (2 ^ (L + 1) - 1) * G)
    (hV' : (∑ i, c' i * (r i : ℤ) = ∑ i, c i * (r i : ℤ)
              + 2 * (2 ^ (L + 1) - 1)) ∨
           (∑ i, c' i * (r i : ℤ) = ∑ i, c i * (r i : ℤ)
              - 2 * (2 ^ (L + 1) - 1))) :
    False := by
  classical
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet L
  have h1 := rival_vector_ne hβ2 hg hv c hfloor hsum hwit
  have h2 := rival_vector_ne hβ2 hg hv c' hfloor' hsum' hwit'
  -- equal filters
  have hfe : (Finset.univ.filter (fun i => Odd (c' i)))
      = Finset.univ.filter (fun i => Odd (c i)) := by
    apply Finset.filter_congr
    intro i _
    exact (hpar i).symm
  rw [hfe] at h2
  set S := ∑ i ∈ Finset.univ.filter (fun i => Odd (c i)), β i with hS
  have hSmem : S = 0 ∨ S = sheet L :=
    sum_mem_pair (two_nsmul_sheet L) _ _ (fun i _ => hβ i)
  obtain ⟨G, hG⟩ := hV
  have hcastV : ((∑ i, c i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) = 0 ∨
      ((∑ i, c i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) = sheet L := by
    rw [hG]
    exact intCast_two_mul_M_mul L G
  have hcastV' : ((∑ i, c' i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4))
      = ((∑ i, c i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + sheet L := by
    rcases hV' with h | h
    · rw [h, Int.cast_add, intCast_two_mul_M]
    · rw [h, sub_eq_add_neg, Int.cast_add, intCast_neg_two_mul_M]
  -- the pinned value
  have hX : ((∑ i, c i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + S
      = sheet L := by
    have hmem := pair_sum_cases hcastV hSmem (two_nsmul_sheet L)
    exact hmem.resolve_left h1
  apply h2
  rw [hcastV']
  have h2s : sheet L + sheet L = 0 := by
    rw [← two_nsmul]
    exact two_nsmul_sheet L
  calc ((∑ i, c i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + sheet L + S
      = (((∑ i, c i * (r i : ℤ) : ℤ) : ZMod (2 ^ (L + 3) - 4)) + S)
        + sheet L := by abel
    _ = sheet L + sheet L := by rw [hX]
    _ = 0 := h2s

end MinModulus
