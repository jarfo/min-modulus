import MinModulus.SILiftRival
import MinModulus.SILiftReduce

/-!
# The explicit rival target

Specializing `siLiftParent` to the actual super-increasing base
`A i = 2 ^ i - 1` turns the rival criterion into a single congruence in the
coin family's VALUE.  Writing `n = m + 2`, a family `κ` on the exponents
`0 .. n - 2` with `n` coins is a rival exactly when

    val(κ) = 2 ^ (n-1) + e + σ(κ) • sheet,     σ(κ) = sheetSum(b, κ).

The target depends on the rival's OWN parity, so there are two of them,
differing by the sheet.  Writing `d = e - (2 ^ (n-1) - 1)` they are
`(2 ^ s - 1) + d + σ • sheet`, which is why `2 ^ s - 1` — the unique
residue `si_digit_cover` cannot reach — is the pivot of the whole
classification: it is the `σ = 0` target exactly when `d = 0`.
-/

namespace MinModulus

open Finset

section Target

variable {m t : ℕ}

/-- The parent over the exact super-increasing child. -/
def siLiftSI (m t : ℕ) (b : ℕ → ℕ) (e : ZMod (siFull m t)) :
    Fin (m + 2) → ZMod (siFull m t) :=
  siLiftParent m t
    (fun i : Fin (m + 1) => ((2 ^ i.val - 1 : ℕ) : ZMod (siFull m t))) b e

private lemma cast_fin_sum (N : ℕ) (f : ℕ → ℕ) (w : ℕ) :
    (∑ i : Fin w, ((f i.val : ℕ) : ZMod N))
      = ((∑ j ∈ range w, f j : ℕ) : ZMod N) := by
  rw [Nat.cast_sum, ← Fin.sum_univ_eq_sum_range
    (fun j => ((f j : ℕ) : ZMod N)) w]

/-- The base sum of the super-increasing block. -/
lemma siLiftSI_base_sum (N : ℕ) :
    (∑ i : Fin (m + 1), ((2 ^ i.val - 1 : ℕ) : ZMod N))
      = ((2 ^ (m + 1) - 1 - (m + 1) : ℕ) : ZMod N) := by
  rw [cast_fin_sum N (fun j => 2 ^ j - 1) (m + 1), sum_si]

/-- The weighted base sum of a coin family. -/
lemma siLiftSI_weighted_base_sum (N : ℕ) (κ : Fin (m + 2) → ℕ) (κ₀ : ℕ → ℕ)
    (hagree : ∀ i : Fin (m + 1), κ i.castSucc = κ₀ i.val) :
    (∑ i : Fin (m + 1), κ i.castSucc • ((2 ^ i.val - 1 : ℕ) : ZMod N))
      = ((val (m + 1) κ₀ - dsum (m + 1) κ₀ : ℕ) : ZMod N) := by
  have h : ∀ i : Fin (m + 1),
      κ i.castSucc • ((2 ^ i.val - 1 : ℕ) : ZMod N)
        = ((κ₀ i.val * (2 ^ i.val - 1) : ℕ) : ZMod N) := by
    intro i
    rw [hagree i, nsmul_eq_mul, Nat.cast_mul]
  rw [Finset.sum_congr rfl (fun i _ => h i),
    cast_fin_sum N (fun j => κ₀ j * (2 ^ j - 1)) (m + 1), sum_mul_si]

/-- **The explicit rival target.**  A family avoiding the extra coordinate
and carrying `m + 2` coins is a rival exactly when its VALUE hits
`2 ^ (m+1) + e`, shifted by the sheet when its sheet sum is odd. -/
theorem siLiftSI_rival_target (b : ℕ → ℕ) (e : ZMod (siFull m t))
    (κ : Fin (m + 2) → ℕ) (κ₀ : ℕ → ℕ)
    (hκ : κ (Fin.last (m + 1)) = 0)
    (hagree : ∀ i : Fin (m + 1), κ i.castSucc = κ₀ i.val)
    (hcount : dsum (m + 1) κ₀ = m + 2)
    (hm : t ≤ m)
    (hrival : ∑ i, κ i • siLiftSI m t b e i = ∑ i, siLiftSI m t b e i) :
    ((val (m + 1) κ₀ : ℕ) : ZMod (siFull m t))
      = ((2 ^ (m + 1) : ℕ) : ZMod (siFull m t)) + e
        + (sheetSum (m + 1) b κ₀) • siSheet m t := by
  have hkey := siLiftParent_rival_sheetSum hm
    (fun i : Fin (m + 1) => ((2 ^ i.val - 1 : ℕ) : ZMod (siFull m t)))
    b e κ κ₀ hκ hagree hrival
  rw [siLiftSI_weighted_base_sum _ κ κ₀ hagree, siLiftSI_base_sum] at hkey
  -- clear both truncated subtractions
  have hle : dsum (m + 1) κ₀ ≤ val (m + 1) κ₀ := si_dsum_le_val _ _
  have hpow : (m + 1) + 1 ≤ 2 ^ (m + 1) := by
    have := Nat.lt_two_pow_self (n := m + 1); omega
  rw [Nat.cast_sub hle, hcount,
    show (2 : ℕ) ^ (m + 1) - 1 - (m + 1) = 2 ^ (m + 1) - (m + 2) from by omega,
    Nat.cast_sub (by omega)] at hkey
  have hcast : ((m + 2 : ℕ) : ZMod (siFull m t))
      = ((m + 2 : ℕ) : ZMod (siFull m t)) := rfl
  linear_combination hkey

/-! ### The exclusion direction -/

/-- **A coin family hitting the target refutes validity.**  Given `κ₀` on
the exponents `0 .. m` with `m + 2` coins whose value hits the target, the
lifted family is a genuine rival, so the parent cannot be valid.

Note no nontriviality check is needed: the all-ones family has `m + 1`
coins, so a family with `m + 2` coins is automatically different from it,
and the lift is zero at the extra coordinate. -/
theorem siLiftSI_not_valid_of_target (hm : t ≤ m) (b κ₀ : ℕ → ℕ)
    (e : ZMod (siFull m t)) (hcount : dsum (m + 1) κ₀ = m + 2)
    (htarget : ((val (m + 1) κ₀ : ℕ) : ZMod (siFull m t))
      = ((2 ^ (m + 1) : ℕ) : ZMod (siFull m t)) + e
        + (sheetSum (m + 1) b κ₀) • siSheet m t) :
    ¬ ValidTuple (siLiftSI m t b e) := by
  intro hv
  set κ : Fin (m + 2) → ℕ :=
    Fin.lastCases 0 (fun i : Fin (m + 1) => κ₀ i.val) with hκdef
  have hlast : κ (Fin.last (m + 1)) = 0 := by simp [hκdef]
  have hagree : ∀ i : Fin (m + 1), κ i.castSucc = κ₀ i.val := by
    intro i; simp [hκdef]
  -- the lifted family has the right number of coins
  have hsum : ∑ i, κ i = m + 2 := by
    rw [Fin.sum_univ_castSucc, hlast, add_zero]
    rw [Finset.sum_congr rfl (fun i _ => hagree i),
      Fin.sum_univ_eq_sum_range κ₀ (m + 1)]
    exact hcount
  -- and it reproduces the total
  have hval : ∑ i, κ i • siLiftSI m t b e i = ∑ i, siLiftSI m t b e i := by
    rw [siLiftSI, siLiftParent_rival_iff _ b e κ hlast,
      siLiftSI_weighted_base_sum _ κ κ₀ hagree, siLiftSI_base_sum]
    have hle : dsum (m + 1) κ₀ ≤ val (m + 1) κ₀ := si_dsum_le_val _ _
    have hpow : (m + 1) + 1 ≤ 2 ^ (m + 1) := by
      have := Nat.lt_two_pow_self (n := m + 1); omega
    rw [Nat.cast_sub hle, hcount,
      show (2 : ℕ) ^ (m + 1) - 1 - (m + 1) = 2 ^ (m + 1) - (m + 2) from by
        omega,
      Nat.cast_sub (by omega)]
    -- the two sheet coefficients differ by `sheetSum`
    have h1 : (∑ i : Fin (m + 1), κ i.castSucc * b i.val)
        = ∑ j ∈ range (m + 1), κ₀ j * b j := by
      rw [← Fin.sum_univ_eq_sum_range (fun j => κ₀ j * b j) (m + 1)]
      exact Finset.sum_congr rfl fun i _ => by rw [hagree i]
    have h2 : (∑ i : Fin (m + 1), b i.val) = ∑ j ∈ range (m + 1), b j :=
      Fin.sum_univ_eq_sum_range b (m + 1)
    rw [h1, h2, htarget]
    have hsheet : (sheetSum (m + 1) b κ₀
          + ∑ j ∈ range (m + 1), κ₀ j * b j) • siSheet m t
        = (∑ j ∈ range (m + 1), b j) • siSheet m t := by
      refine nsmul_siSheet_congr hm ?_
      have := sheetSum_weighted (m + 1) b κ₀
      omega
    rw [← hsheet, add_smul]
    abel
  -- validity would force every multiplicity to be one
  have h1 := hv κ hsum hval (Fin.last (m + 1))
  rw [hlast] at h1
  exact absurd h1 (by norm_num)

end Target

end MinModulus
