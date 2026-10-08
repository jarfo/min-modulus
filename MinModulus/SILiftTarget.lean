import MinModulus.SILiftRival
import MinModulus.SILiftReduce
import MinModulus.SILiftDigit

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

/-! ### The constant-sheet case, at the lift

When the sheet bits are constant the rival's parity is constant too
(`si_sheet_parity_const`), so there is only ONE target, and
`si_digit_cover` hits every residue but `2 ^ s - 1`.  Validity therefore
pins the target to that one unreachable residue, and unwinding gives the
classification: the extra reduces to the next super-increasing entry. -/

theorem siLiftSI_affine_of_const (hm : t ≤ m) (hm3 : 3 ≤ m) (ht : 1 ≤ t)
    (hsn : 2 ^ (t + 1) ≤ m + 2) (β : ℕ) (b : ℕ → ℕ) (hb : ∀ i, b i = β)
    (e : ZMod (siFull m t)) (hv : ValidTuple (siLiftSI m t b e)) :
    siReduce hm e
      = siReduce hm ((2 ^ (m + 1) - 1 : ℕ) : ZMod (siFull m t)) := by
  haveI : NeZero (siFull m t) := ⟨by have := siFull_pos hm; omega⟩
  obtain ⟨T, hT⟩ : ∃ T : ZMod (siFull m t),
      T = ((2 ^ (m + 1) : ℕ) : ZMod (siFull m t)) + e + β • siSheet m t :=
    ⟨_, rfl⟩
  -- the target must be the one residue `si_digit_cover` cannot reach
  have hval : T.val = 2 ^ (t + 1) - 1 := by
    by_contra hne
    have hTlt : T.val < 2 ^ (m + 2) - 2 ^ (t + 1) := by
      have h := ZMod.val_lt T
      unfold siFull at h
      exact h
    obtain ⟨κ₀, hd, hvmod⟩ :=
      si_digit_cover (n := m + 2) (s := t + 1) (r := T.val)
        (by omega) (by omega) hsn hTlt hne
    rw [show m + 2 - 1 = m + 1 from by omega] at hd hvmod
    refine siLiftSI_not_valid_of_target hm b κ₀ e hd ?_ hv
    have hsheet : (sheetSum (m + 1) b κ₀) • siSheet m t
        = β • siSheet m t := by
      refine nsmul_siSheet_congr hm ?_
      have hfil : sheetSum (m + 1) b κ₀
          = ∑ _i ∈ (range (m + 1)).filter (fun i => κ₀ i % 2 = 0), β := by
        unfold sheetSum
        rw [Finset.sum_filter]
        exact Finset.sum_congr rfl fun i _ => by rw [hb i]
      rw [hfil]
      exact si_sheet_parity_const (m + 1) κ₀ hd β
    rw [hsheet, ← hT]
    have hmod : val (m + 1) κ₀ % siFull m t = T.val := by
      unfold siFull; exact hvmod
    calc ((val (m + 1) κ₀ : ℕ) : ZMod (siFull m t))
        = ((val (m + 1) κ₀ % siFull m t : ℕ) : ZMod (siFull m t)) :=
          (ZMod.natCast_mod _ _).symm
      _ = ((T.val : ℕ) : ZMod (siFull m t)) := by rw [hmod]
      _ = T := ZMod.natCast_rightInverse T
  -- unwind: the target IS `2 ^ s - 1`, so `e` is pinned modulo the sheet
  have hTeq : T = ((2 ^ (t + 1) - 1 : ℕ) : ZMod (siFull m t)) := by
    rw [← hval]; exact (ZMod.natCast_rightInverse T).symm
  have he : e = ((2 ^ (t + 1) - 1 : ℕ) : ZMod (siFull m t))
      - ((2 ^ (m + 1) : ℕ) : ZMod (siFull m t)) - β • siSheet m t := by
    rw [← hTeq, hT]; ring
  rw [he, map_sub, map_sub, map_nsmul, siReduce_sheet hm, smul_zero, sub_zero]
  -- `2 ^ (t+1) - 1 = (2 ^ (m+1) - 1) + 2 ^ (m+1) - siFull` as naturals
  have hkey : ((2 ^ (t + 1) - 1 : ℕ) : ZMod (siFull m t))
      = (((2 ^ (m + 1) - 1) + 2 ^ (m + 1) - siFull m t : ℕ) :
          ZMod (siFull m t)) := by
    congr 1
    have h1 : (1 : ℕ) ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
    have h3 : (2 : ℕ) ^ (t + 1) ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hNv : siFull m t = 2 ^ (m + 2) - 2 ^ (t + 1) := rfl
    have hp : (2 : ℕ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
    omega
  rw [hkey, Nat.cast_sub (by
      have h1 : (1 : ℕ) ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
      have hNv : siFull m t = 2 ^ (m + 2) - 2 ^ (t + 1) := rfl
      have hp : (2 : ℕ) ^ (m + 2) = 2 * 2 ^ (m + 1) := by ring
      have h2 : (1 : ℕ) ≤ 2 ^ (t + 1) := Nat.one_le_pow _ _ (by norm_num)
      omega),
    Nat.cast_add, ZMod.natCast_self]
  simp only [map_sub, map_add, map_zero, sub_zero]
  abel

end Target

end MinModulus
