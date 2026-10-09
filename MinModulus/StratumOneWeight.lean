/-
Copyright (c) 2026 José A. R. Fonollosa. All rights reserved.
Released under Apache 2.0 license.
-/
import MinModulus.StratumOneRivals

/-!
# Binary supports modulo a Mersenne number

The stratum-one exclusion of `StratumOneRivals` takes the support `T` of the
extra residue as an input.  This file produces that support from the residue
itself: every element of `ZMod (2 ^ d - 1)` is the sum of `pow2` over a set of
fewer than `d` indices.  Consequently the exclusion applies whenever the extra
residue `e` has `e + 1` neither zero nor a single power of two -- that is,
whenever its binary weight is at least two.
-/

namespace MinModulus

namespace StratumOne

open Finset

/-- Every natural number below `2 ^ d` is a sum of distinct powers of two with
exponents below `d`. -/
theorem exists_binary_support : ∀ (d v : ℕ), v < 2 ^ d →
    ∃ S : Finset (Fin d), ∑ i ∈ S, 2 ^ (i : ℕ) = v := by
  intro d
  induction d with
  | zero => intro v hv; exact ⟨∅, by simp; omega⟩
  | succ d ih =>
    intro v hv
    have hcs : ∀ (S : Finset (Fin d)), ∑ i ∈ S.image Fin.castSucc, 2 ^ (i : ℕ)
        = ∑ i ∈ S, 2 ^ (i : ℕ) := by
      intro S
      rw [Finset.sum_image (fun x _ y _ hxy => Fin.castSucc_injective d hxy)]
      simp
    rcases Nat.lt_or_ge v (2 ^ d) with h | h
    · obtain ⟨S, hS⟩ := ih v h
      exact ⟨S.image Fin.castSucc, by rw [hcs S, hS]⟩
    · obtain ⟨S, hS⟩ := ih (v - 2 ^ d) (by rw [pow_succ] at hv; omega)
      have hnm : Fin.last d ∉ S.image Fin.castSucc := by
        simp only [Finset.mem_image, not_exists]
        intro i
        simp only [not_and]
        intro _
        exact Fin.castSucc_lt_last i |>.ne
      refine ⟨insert (Fin.last d) (S.image Fin.castSucc), ?_⟩
      rw [Finset.sum_insert hnm, hcs S, hS, Fin.val_last]
      omega

/-- The full binary support sums to `2 ^ d - 1`. -/
theorem sum_univ_two_pow (d : ℕ) : ∑ i : Fin d, 2 ^ (i : ℕ) = 2 ^ d - 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    have h : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, pow_succ]
    omega

variable {d : ℕ} [NeZero d]

/-- Every residue modulo `2 ^ d - 1` is the `pow2`-sum over a set of fewer than
`d` indices: its binary support. -/
theorem exists_pow2_support (u : ZMod (2 ^ d - 1)) :
    ∃ S : Finset (ZMod d), S.card < d ∧ ∑ s ∈ S, pow2 s = u := by
  classical
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have h2d : 2 ≤ 2 ^ d := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hd
  haveI : NeZero (2 ^ d - 1) := ⟨by omega⟩
  have hv : u.val < 2 ^ d - 1 := ZMod.val_lt u
  obtain ⟨S, hS⟩ := exists_binary_support d u.val (by omega)
  have hSne : S ≠ Finset.univ := by
    intro h
    rw [h, sum_univ_two_pow] at hS
    omega
  have hcard : S.card < d := by
    rcases Nat.lt_or_ge S.card d with h | h
    · exact h
    · exact absurd (Finset.eq_univ_of_card S
        (le_antisymm (by simpa using Finset.card_le_univ S) (by simpa using h))) hSne
  have hinj : Function.Injective (fun i : Fin d => ((i : ℕ) : ZMod d)) := by
    intro i j hij
    have := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt i.isLt, ZMod.val_natCast_of_lt j.isLt] at this
    exact Fin.ext this
  refine ⟨S.image (fun i : Fin d => ((i : ℕ) : ZMod d)), ?_, ?_⟩
  · rwa [Finset.card_image_of_injective _ hinj]
  · rw [Finset.sum_image (fun x _ y _ hxy => hinj hxy)]
    have hterm : ∀ i : Fin d, pow2 ((i : ℕ) : ZMod d)
        = ((2 ^ (i : ℕ) : ℕ) : ZMod (2 ^ d - 1)) := by
      intro i; rw [pow2_natCast]; push_cast; ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← Nat.cast_sum, hS]
    simp

omit [NeZero d] in
/-- Shifting a binary support by one keeps its size and its shifted `pow2`-sum. -/
theorem card_image_add_one (S : Finset (ZMod d)) :
    (S.image (fun s => s + 1)).card = S.card :=
  Finset.card_image_of_injective _ (add_left_injective 1)

omit [NeZero d] in
theorem sum_pow2_pred_image (S : Finset (ZMod d)) :
    ∑ t ∈ S.image (fun s => s + 1), pow2 (t - 1) = ∑ s ∈ S, pow2 s := by
  classical
  rw [Finset.sum_image (fun x _ y _ hxy => add_left_injective 1 hxy)]
  simp

/-- **Stratum-one exclusion, weight form.**  At the first even stratum
`2 * (2 ^ d - 1) = 2 ^ (d + 1) - 2`, a tuple whose first `d` entries reduce to
the super-increasing block `2 ^ i - 1` modulo `M = 2 ^ d - 1` cannot be valid
once the shifted residue `e + 1` of its last entry is neither zero nor a single
power of two -- that is, once its binary weight is at least two.

This is the first branch of the stratum-one trichotomy, with no combinatorial
input left: the support of the extra residue is produced from the residue. -/
theorem not_validTuple_of_extra_weight
    (g : Fin (d + 1) → ZMod (2 * (2 ^ d - 1)))
    (hblk : ∀ i : Fin d, ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g i.castSucc) = 2 ^ (i : ℕ) - 1)
    (hne0 : ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g (Fin.last d)) + 1 ≠ 0)
    (hnepow : ∀ k : ZMod d, ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1))
      (g (Fin.last d)) + 1 ≠ pow2 k) :
    ¬ ValidTuple g := by
  classical
  obtain ⟨S, hcard, hsum⟩ := exists_pow2_support
    (ZMod.castHom (dvd_mul_left (2 ^ d - 1) 2) (ZMod (2 ^ d - 1)) (g (Fin.last d)) + 1)
  have h2 : 2 ≤ S.card := by
    rcases Nat.lt_or_ge S.card 2 with h | h
    · interval_cases hc : S.card
      · rw [Finset.card_eq_zero.mp hc] at hsum
        exact absurd hsum.symm hne0
      · obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hc
        rw [ha] at hsum
        simp only [Finset.sum_singleton] at hsum
        exact absurd hsum.symm (hnepow a)
    · exact h
  refine not_validTuple_of_superIncreasing_block g hblk
    (S.image (fun s => s + 1)) ?_ ?_ ?_
  · rwa [card_image_add_one]
  · rwa [card_image_add_one]
  · rw [sum_pow2_pred_image, hsum]
    ring

end StratumOne

end MinModulus
