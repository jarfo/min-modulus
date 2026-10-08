import MinModulus.SILiftParity

/-!
# The parity-flipping move

A coin family can be modified at three consecutive exponents by
`(-2, +3, -1)` at `(c-1, c, c+1)` without changing either its value or its
coin count:

    -2 * 2^(c-1) + 3 * 2^c - 2^(c+1) = 0,      -2 + 3 - 1 = 0.

The move toggles the parity of the multiplicities at `c` and `c+1` and
leaves the one at `c-1` alone, so it shifts the sheet parity by
`b c + b (c+1)`.  When `b` is non-constant some adjacent pair differs, and
the move flips the sheet parity — which is why only a CONSTANT sheet bit
can pin the parity, and hence why only constant-bit lifts keep an extra.
-/

namespace MinModulus

open Finset

/-- Updating one coin count, in additive form. -/
lemma val_update (w j v : ℕ) (k : ℕ → ℕ) (hj : j < w) :
    val w (Function.update k j v) + k j * 2 ^ j = val w k + v * 2 ^ j := by
  unfold val
  have hmem : j ∈ range w := Finset.mem_range.mpr hj
  rw [← Finset.add_sum_erase (range w)
        (fun i => Function.update k j v i * 2 ^ i) hmem,
      ← Finset.add_sum_erase (range w) (fun i => k i * 2 ^ i) hmem]
  have hcong : ∑ i ∈ (range w).erase j, Function.update k j v i * 2 ^ i
      = ∑ i ∈ (range w).erase j, k i * 2 ^ i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [Function.update_self]
  rw [hcong]
  ring

/-- Updating one coin count, for the coin total. -/
lemma dsum_update (w j v : ℕ) (k : ℕ → ℕ) (hj : j < w) :
    dsum w (Function.update k j v) + k j = dsum w k + v := by
  unfold dsum
  have hmem : j ∈ range w := Finset.mem_range.mpr hj
  rw [← Finset.add_sum_erase (range w) (fun i => Function.update k j v i) hmem,
      ← Finset.add_sum_erase (range w) (fun i => k i) hmem]
  have hcong : ∑ i ∈ (range w).erase j, Function.update k j v i
      = ∑ i ∈ (range w).erase j, k i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  simp only [Function.update_self]
  rw [hcong]
  ring

/-- The three-point move at consecutive exponents `c-1, c, c+1`. -/
def flipMove (k : ℕ → ℕ) (c : ℕ) : ℕ → ℕ :=
  Function.update
    (Function.update (Function.update k (c - 1) (k (c - 1) - 2)) c (k c + 3))
    (c + 1) (k (c + 1) - 1)

lemma flipMove_apply_of_ne (k : ℕ → ℕ) (c i : ℕ)
    (h1 : i ≠ c - 1) (h2 : i ≠ c) (h3 : i ≠ c + 1) :
    flipMove k c i = k i := by
  unfold flipMove
  rw [Function.update_of_ne h3, Function.update_of_ne h2,
    Function.update_of_ne h1]

lemma flipMove_at_pred (k : ℕ → ℕ) (c : ℕ) (hc : 1 ≤ c) :
    flipMove k c (c - 1) = k (c - 1) - 2 := by
  unfold flipMove
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
    Function.update_self]

lemma flipMove_at (k : ℕ → ℕ) (c : ℕ) :
    flipMove k c c = k c + 3 := by
  unfold flipMove
  rw [Function.update_of_ne (by omega), Function.update_self]

lemma flipMove_at_succ (k : ℕ → ℕ) (c : ℕ) :
    flipMove k c (c + 1) = k (c + 1) - 1 := by
  unfold flipMove
  rw [Function.update_self]

section Move

variable {m c : ℕ} {k : ℕ → ℕ}

private lemma mid_at_succ (hc : 1 ≤ c) :
    (Function.update (Function.update k (c - 1) (k (c - 1) - 2)) c
      (k c + 3)) (c + 1) = k (c + 1) := by
  rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]

private lemma pred_at (hc : 1 ≤ c) :
    (Function.update k (c - 1) (k (c - 1) - 2)) c = k c := by
  rw [Function.update_of_ne (by omega)]

/-- The move preserves the coin value. -/
theorem flipMove_val (hc : 1 ≤ c) (hcm : c + 1 < m)
    (h1 : 2 ≤ k (c - 1)) (h2 : 1 ≤ k (c + 1)) :
    val m (flipMove k c) = val m k := by
  have e1 := val_update m (c - 1) (k (c - 1) - 2) k (by omega)
  have e2 := val_update m c (k c + 3)
    (Function.update k (c - 1) (k (c - 1) - 2)) (by omega)
  have e3 := val_update m (c + 1) (k (c + 1) - 1)
    (Function.update (Function.update k (c - 1) (k (c - 1) - 2)) c (k c + 3))
    (by omega)
  rw [pred_at hc] at e2
  rw [mid_at_succ hc] at e3
  have hr1 : k (c - 1) - 2 + 2 = k (c - 1) := by omega
  have hr2 : k (c + 1) - 1 + 1 = k (c + 1) := by omega
  have p1 : (k (c - 1) - 2) * 2 ^ (c - 1) + 2 * 2 ^ (c - 1)
      = k (c - 1) * 2 ^ (c - 1) := by rw [← Nat.add_mul, hr1]
  have p2 : (k (c + 1) - 1) * 2 ^ (c + 1) + 1 * 2 ^ (c + 1)
      = k (c + 1) * 2 ^ (c + 1) := by rw [← Nat.add_mul, hr2]
  have hpc : (2 : ℕ) ^ c = 2 * 2 ^ (c - 1) := by
    have hps := pow_succ 2 (c - 1)
    rw [show c - 1 + 1 = c from by omega] at hps
    omega
  have hpc1 : (2 : ℕ) ^ (c + 1) = 2 * 2 ^ c := by rw [pow_succ]; ring
  have hexp : (k c + 3) * 2 ^ c = k c * 2 ^ c + 3 * 2 ^ c := by ring
  rw [hexp] at e2
  show val m (Function.update (Function.update
    (Function.update k (c - 1) (k (c - 1) - 2)) c (k c + 3))
    (c + 1) (k (c + 1) - 1)) = val m k
  omega

/-- The move preserves the coin count. -/
theorem flipMove_dsum (hc : 1 ≤ c) (hcm : c + 1 < m)
    (h1 : 2 ≤ k (c - 1)) (h2 : 1 ≤ k (c + 1)) :
    dsum m (flipMove k c) = dsum m k := by
  have e1 := dsum_update m (c - 1) (k (c - 1) - 2) k (by omega)
  have e2 := dsum_update m c (k c + 3)
    (Function.update k (c - 1) (k (c - 1) - 2)) (by omega)
  have e3 := dsum_update m (c + 1) (k (c + 1) - 1)
    (Function.update (Function.update k (c - 1) (k (c - 1) - 2)) c (k c + 3))
    (by omega)
  rw [pred_at hc] at e2
  rw [mid_at_succ hc] at e3
  show dsum m (Function.update (Function.update
    (Function.update k (c - 1) (k (c - 1) - 2)) c (k c + 3))
    (c + 1) (k (c + 1) - 1)) = dsum m k
  omega

/-- The sheet contribution of a rival: the bits at even multiplicities. -/
def sheetSum (m : ℕ) (b k : ℕ → ℕ) : ℕ :=
  ∑ i ∈ range m, (if k i % 2 = 0 then b i else 0)

/-- Splitting a range sum at two consecutive points. -/
private lemma sum_split_two (f : ℕ → ℕ) (hcm : c + 1 < m) :
    ∑ i ∈ range m, f i
      = f c + (f (c + 1)
        + ∑ i ∈ ((range m).erase c).erase (c + 1), f i) := by
  have hc : c ∈ range m := Finset.mem_range.mpr (by omega)
  have hc1 : c + 1 ∈ (range m).erase c :=
    Finset.mem_erase.mpr ⟨by omega, Finset.mem_range.mpr (by omega)⟩
  rw [← Finset.add_sum_erase (range m) f hc,
    ← Finset.add_sum_erase ((range m).erase c) f hc1]

/-- Off `{c, c+1}` the move does not change any multiplicity parity. -/
private lemma flipMove_parity_off (hc : 1 ≤ c) (h1 : 2 ≤ k (c - 1))
    {i : ℕ} (hi : i ≠ c) (hi1 : i ≠ c + 1) :
    flipMove k c i % 2 = k i % 2 := by
  by_cases hp : i = c - 1
  · subst hp
    rw [flipMove_at_pred k c hc]
    omega
  · rw [flipMove_apply_of_ne k c i hp hi hi1]

/-- **The move shifts the sheet parity by `b c + b (c+1)`.**  So when the
sheet bits differ at some adjacent pair, the move flips the sheet
parity. -/
theorem flipMove_sheetSum (b : ℕ → ℕ) (hc : 1 ≤ c) (hcm : c + 1 < m)
    (h1 : 2 ≤ k (c - 1)) (h2 : 1 ≤ k (c + 1)) :
    (sheetSum m b (flipMove k c) + sheetSum m b k) % 2
      = (b c + b (c + 1)) % 2 := by
  classical
  unfold sheetSum
  rw [sum_split_two (fun i => if flipMove k c i % 2 = 0 then b i else 0) hcm,
    sum_split_two (fun i => if k i % 2 = 0 then b i else 0) hcm]
  have hrest : ∑ i ∈ ((range m).erase c).erase (c + 1),
        (if flipMove k c i % 2 = 0 then b i else 0)
      = ∑ i ∈ ((range m).erase c).erase (c + 1),
        (if k i % 2 = 0 then b i else 0) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi1 : i ≠ c + 1 := Finset.ne_of_mem_erase hi
    have hi0 : i ≠ c := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hi)
    rw [flipMove_parity_off hc h1 hi0 hi1]
  rw [hrest]
  have hAc : flipMove k c c = k c + 3 := flipMove_at k c
  have hAs : flipMove k c (c + 1) = k (c + 1) - 1 := flipMove_at_succ k c
  rw [hAc, hAs]
  have hA : (if (k c + 3) % 2 = 0 then b c else 0)
      + (if k c % 2 = 0 then b c else 0) = b c := by
    by_cases hkc : k c % 2 = 0
    · rw [if_neg (by omega), if_pos hkc]; omega
    · rw [if_pos (by omega), if_neg hkc]; omega
  have hB : (if (k (c + 1) - 1) % 2 = 0 then b (c + 1) else 0)
      + (if k (c + 1) % 2 = 0 then b (c + 1) else 0) = b (c + 1) := by
    by_cases hkc : k (c + 1) % 2 = 0
    · rw [if_neg (by omega), if_pos hkc]; omega
    · rw [if_pos (by omega), if_neg hkc]; omega
  omega

/-- **The move as a rival transformer.**  Applied to a coin family realizing
a given target with a given coin count, it returns another family realizing
the SAME target with the SAME count but the OPPOSITE sheet parity, provided
the sheet bits differ at the adjacent pair `(c, c+1)`.

This is the exact interface the parity-refined digit lemma has to feed: it
must supply, for a prescribed non-constant adjacent pair, a realizing family
with at least two coins at `c-1` and at least one at `c+1`. -/
theorem flipMove_rival (b : ℕ → ℕ) (hc : 1 ≤ c) (hcm : c + 1 < m)
    (h1 : 2 ≤ k (c - 1)) (h2 : 1 ≤ k (c + 1))
    (hne : b c % 2 ≠ b (c + 1) % 2) :
    dsum m (flipMove k c) = dsum m k
      ∧ val m (flipMove k c) = val m k
      ∧ sheetSum m b (flipMove k c) % 2 ≠ sheetSum m b k % 2 := by
  refine ⟨flipMove_dsum hc hcm h1 h2, flipMove_val hc hcm h1 h2, ?_⟩
  have h := flipMove_sheetSum b hc hcm h1 h2
  omega

end Move

end MinModulus
