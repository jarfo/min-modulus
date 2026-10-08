import MinModulus.RLiftBits
import MinModulus.ReflectedFamily

/-!
# The power chain: reflected lifts with extra `2^(m+1)` are invalid

Setting: `m ≥ 2` even, `M = 2^(m+1) - 1`, parent modulus `N = 4M`.
The parent tuple `g` has `m + 3` coordinates: the first `m + 2` lift the
reflected child `(0, 1, M-1, M-3, …, M-(2^m - 1))` from `ZMod 2M` (one
free sheet bit each), and the last is the extra, here congruent to
`2^(m+1)` modulo `2M`.

This file proves such a parent is never a valid tuple, by the power
chain: the exact identities `2 τ_a - τ_{a+1} = 2^(m+1)` (with
`τ_a = M - (2^a - 1)`) make each chain rival's value a pure sheet term,
so validity pins every sheet bit; a final all-drop rival then closes.
-/

namespace MinModulus

open Finset

/-- Integer representatives of the reflected child: `0, 1`, then
`τ_j = M - (2^(j+1) - 1)` for `j < m`. -/
def rliftChild (m : ℕ) : Fin (m + 2) → ℕ :=
  Fin.cons 0 (Fin.cons 1
    (fun j : Fin m => 2 ^ (m + 1) - 1 - (2 ^ (j.val + 1) - 1)))

/-- The parent modulus is four times the half order. -/
lemma rlift_modulus (m : ℕ) : 2 ^ (m + 3) - 4 = 4 * (2 ^ (m + 1) - 1) := by
  have h : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
  have hpow : 2 ^ (m + 3) = 4 * 2 ^ (m + 1) := by ring
  omega

/-- The sheet element: the half order `2M` inside `ZMod (4M)`. -/
def sheet (m : ℕ) : ZMod (2 ^ (m + 3) - 4) :=
  ((2 * (2 ^ (m + 1) - 1) : ℕ) : ZMod (2 ^ (m + 3) - 4))

/-- The sheet element is 2-torsion. -/
lemma two_nsmul_sheet (m : ℕ) : 2 • sheet m = 0 := by
  have : 2 • sheet m
      = ((2 * (2 * (2 ^ (m + 1) - 1)) : ℕ) : ZMod (2 ^ (m + 3) - 4)) := by
    rw [sheet]
    push_cast
    ring
  rw [this]
  have h4 : 2 * (2 * (2 ^ (m + 1) - 1)) = 2 ^ (m + 3) - 4 := by
    have := rlift_modulus m
    omega
  rw [h4]
  exact ZMod.natCast_self _

/-- Integer representatives of the whole parent: the reflected child
followed by the extra `2^(m+1)`. -/
def rliftParent (m : ℕ) : Fin (m + 3) → ℕ :=
  Fin.cons 0 (Fin.cons 1
    (Fin.snoc (fun j : Fin m => 2 ^ (m + 1) - 1 - (2 ^ (j.val + 1) - 1))
      (2 ^ (m + 1))))

/-- Coordinate of the `j`-th tail coin inside the parent. -/
def tauC (m : ℕ) (j : ℕ) (h : j < m) : Fin (m + 3) := ⟨j + 2, by omega⟩

/-- The extra's coordinate. -/
def extraC (m : ℕ) : Fin (m + 3) := Fin.last (m + 2)

lemma rliftParent_zero (m : ℕ) : rliftParent m ⟨0, by omega⟩ = 0 := rfl

lemma rliftParent_one (m : ℕ) : rliftParent m ⟨1, by omega⟩ = 1 := rfl

lemma rliftParent_tau (m : ℕ) (j : ℕ) (h : j < m) :
    rliftParent m (tauC m j h) = 2 ^ (m + 1) - 1 - (2 ^ (j + 1) - 1) := by
  have h1 : (tauC m j h) = Fin.succ (Fin.succ ⟨j, by omega⟩) := by
    apply Fin.ext; simp [tauC, Fin.succ]
  rw [h1, rliftParent, Fin.cons_succ, Fin.cons_succ]
  have h2 : (⟨j, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨j, h⟩ := by
    apply Fin.ext; simp
  rw [h2, Fin.snoc_castSucc]

lemma rliftParent_last (m : ℕ) :
    rliftParent m (extraC m) = 2 ^ (m + 1) := by
  have h1 : extraC m = Fin.succ (Fin.succ (Fin.last m)) := by
    apply Fin.ext; simp [extraC, Fin.succ]
  rw [h1, rliftParent, Fin.cons_succ, Fin.cons_succ, Fin.snoc_last]

/-- The sheet is nonzero. -/
lemma sheet_ne_zero (m : ℕ) : sheet m ≠ 0 := by
  rw [sheet, Ne, ZMod.natCast_eq_zero_iff]
  intro hdvd
  have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
  have h4 := rlift_modulus m
  have hle := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Core inequality for the three-point rival `p ↦ 3, q ↦ 0, s ↦ 0`:
by validity, its value — integer part plus the two odd-coefficient
bits — is nonzero. -/
lemma rival_three_ne (m : ℕ)
    (g β : Fin (m + 3) → ZMod (2 ^ (m + 3) - 4))
    (hβ2 : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((rliftParent m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i)
    (hv : ValidTuple g) (p q s : Fin (m + 3))
    (hpq : p ≠ q) (hps : p ≠ s) (hqs : q ≠ s) :
    (((2 * (rliftParent m p : ℤ) - rliftParent m q - rliftParent m s) : ℤ) :
        ZMod (2 ^ (m + 3) - 4)) + (β q + β s) ≠ 0 := by
  classical
  set κ : Fin (m + 3) → ℕ :=
    fun i => if i = p then 3 else if i = q then 0 else if i = s then 0 else 1 with hκ
  have hκp : κ p = 3 := by simp [hκ]
  have hκq : κ q = 0 := by simp [hκ, Ne.symm hpq]
  have hκs : κ s = 0 := by simp [hκ, Ne.symm hps, Ne.symm hqs]
  have hκo : ∀ i, i ≠ p → i ≠ q → i ≠ s → κ i = 1 := by
    intro i h1 h2 h3; simp [hκ, h1, h2, h3]
  have hκsum : ∑ i, κ i = m + 3 := by
    rw [sum_split_three κ p q s hpq hps hqs, hκp, hκq, hκs]
    have hrest : ∑ i ∈ Finset.univ \ {p, q, s}, κ i
        = (Finset.univ \ ({p, q, s} : Finset (Fin (m + 3)))).card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hi
      exact hκo i hi.2.1 hi.2.2.1 hi.2.2.2
    have hc3 : ({p, q, s} : Finset (Fin (m + 3))).card = 3 := by
      rw [Finset.card_insert_of_notMem (by simp [hpq, hps]),
          Finset.card_insert_of_notMem (by simp [hqs]), Finset.card_singleton]
    rw [hrest, Finset.card_sdiff, Finset.inter_univ, hc3, Finset.card_univ,
        Fintype.card_fin]
    omega
  have hne := validTuple_no_shifted_rival hv κ hκsum (j := p)
    (by rw [hκp]; norm_num)
  rw [shifted_sum_eq (fun i => (κ i : ℤ) - 1) (rliftParent m) β g hβ2 hg] at hne
  have hints : ∑ i, ((κ i : ℤ) - 1) * (rliftParent m i : ℤ)
      = 2 * (rliftParent m p : ℤ) - rliftParent m q - rliftParent m s := by
    rw [sum_eq_of_three (fun i => ((κ i : ℤ) - 1) * (rliftParent m i : ℤ))
      p q s hpq hps hqs (by
        intro i h1 h2 h3
        simp [hκo i h1 h2 h3])]
    rw [hκp, hκq, hκs]
    push_cast
    ring
  have hfilter : ∑ i ∈ Finset.univ.filter (fun i => Odd ((κ i : ℤ) - 1)), β i
      = β q + β s := by
    rw [Finset.sum_filter]
    rw [sum_eq_of_two (fun i => if Odd ((κ i : ℤ) - 1) then β i else 0)
      q s hqs (by
        intro i h2 h3
        by_cases h1 : i = p
        · subst h1
          rw [hκp]
          norm_num
        · rw [hκo i h1 h2 h3]
          norm_num)]
    rw [hκq, hκs]
    norm_num
  rw [hints, hfilter] at hne
  exact fun h => hne (by rw [← h])

section Pins

variable {m : ℕ} {g β : Fin (m + 3) → ZMod (2 ^ (m + 3) - 4)}

/-- Chain pin: for adjacent tail coins, the exact identity
`2 τ_j - τ_{j+1} = 2^(m+1)` forces the sheet bits of `τ_{j+1}` and the
extra to differ. -/
lemma chain_pin (hβ : ∀ i, β i = 0 ∨ β i = sheet m)
    (hg : ∀ i, g i = ((rliftParent m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i)
    (hv : ValidTuple g) (j : ℕ) (hj : j + 1 < m) :
    β (tauC m (j + 1) hj) + β (extraC m) = sheet m := by
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet m
  have hd1 : tauC m j (by omega) ≠ tauC m (j + 1) hj := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd2 : tauC m j (by omega) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this; omega
  have hd3 : tauC m (j + 1) hj ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this; omega
  have h := rival_three_ne m g β hβ2 hg hv _ _ _ hd1 hd2 hd3
  rw [rliftParent_tau m j (by omega), rliftParent_tau m (j + 1) hj,
      rliftParent_last] at h
  have hz : (2 * ((2 ^ (m + 1) - 1 - (2 ^ (j + 1) - 1) : ℕ) : ℤ)
      - ((2 ^ (m + 1) - 1 - (2 ^ (j + 1 + 1) - 1) : ℕ) : ℤ)
      - ((2 ^ (m + 1) : ℕ) : ℤ)) = 0 := by
    have hb1 : 2 ^ (j + 1) ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb2 : 2 ^ (j + 1 + 1) ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hp1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
    push_cast [Nat.cast_sub (by omega : 2 ^ (j + 1) - 1 ≤ 2 ^ (m + 1) - 1),
      Nat.cast_sub (by omega : 2 ^ (j + 1 + 1) - 1 ≤ 2 ^ (m + 1) - 1),
      Nat.cast_sub hp1, Nat.cast_sub (by omega : 1 ≤ 2 ^ (j + 1 + 1)),
      Nat.cast_sub (by omega : 1 ≤ 2 ^ (m + 1))]
    ring
  rw [hz] at h
  simp only [Int.cast_zero, zero_add] at h
  exact pair_sum_eq_of_ne_zero (hβ _) (hβ _) (two_nsmul_sheet m) h

/-- Top pin: `2 τ_{m-1} = 2^(m+1)` (the top coin is the power `2^m`)
forces the bits of coordinate zero and the extra to differ. -/
lemma top_pin (hm : 1 ≤ m) (hβ : ∀ i, β i = 0 ∨ β i = sheet m)
    (hg : ∀ i, g i = ((rliftParent m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i)
    (hv : ValidTuple g) :
    β ⟨0, by omega⟩ + β (extraC m) = sheet m := by
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet m
  have hd1 : tauC m (m - 1) (by omega) ≠ (⟨0, by omega⟩ : Fin (m + 3)) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd2 : tauC m (m - 1) (by omega) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this; omega
  have hd3 : (⟨0, by omega⟩ : Fin (m + 3)) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [extraC] at this
  have h := rival_three_ne m g β hβ2 hg hv _ _ _ hd1 hd2 hd3
  rw [rliftParent_tau m (m - 1) (by omega), rliftParent_zero,
      rliftParent_last] at h
  have hz : (2 * ((2 ^ (m + 1) - 1 - (2 ^ (m - 1 + 1) - 1) : ℕ) : ℤ)
      - ((0 : ℕ) : ℤ) - ((2 ^ (m + 1) : ℕ) : ℤ)) = 0 := by
    have hm1 : m - 1 + 1 = m := by omega
    rw [hm1]
    have hb1 : 2 ^ m ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hp1 : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
    push_cast [Nat.cast_sub (by omega : 2 ^ m - 1 ≤ 2 ^ (m + 1) - 1),
      Nat.cast_sub hp1, Nat.cast_sub (by omega : 1 ≤ 2 ^ (m + 1))]
    rw [show ((2 : ℤ) ^ (m + 1)) = 2 * 2 ^ m from by ring]
    ring
  rw [hz] at h
  simp only [Int.cast_zero, zero_add] at h
  exact pair_sum_eq_of_ne_zero (hβ _) (hβ _) (two_nsmul_sheet m) h

/-- Bottom pin: `τ_0 + 2^(m+1) = 2M` forces the bits of the first tail
coin and the extra to agree. -/
lemma bottom_pin (hm : 1 ≤ m) (hβ : ∀ i, β i = 0 ∨ β i = sheet m)
    (hg : ∀ i, g i = ((rliftParent m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i)
    (hv : ValidTuple g) :
    β (tauC m 0 (by omega)) + β (extraC m) = 0 := by
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet m
  have hd1 : (⟨0, by omega⟩ : Fin (m + 3)) ≠ tauC m 0 (by omega) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd2 : (⟨0, by omega⟩ : Fin (m + 3)) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [extraC] at this
  have hd3 : tauC m 0 (by omega) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this; omega
  have h := rival_three_ne m g β hβ2 hg hv _ _ _ hd1 hd2 hd3
  rw [rliftParent_tau m 0 (by omega), rliftParent_zero, rliftParent_last] at h
  have hz : (2 * ((0 : ℕ) : ℤ)
      - ((2 ^ (m + 1) - 1 - (2 ^ (0 + 1) - 1) : ℕ) : ℤ)
      - ((2 ^ (m + 1) : ℕ) : ℤ))
      = -(2 * (2 ^ (m + 1) - 1 : ℤ)) := by
    have hb1 : (2 : ℕ) ≤ 2 ^ (m + 1) := by
      have := Nat.pow_le_pow_right (show 1 ≤ 2 by norm_num) (show 1 ≤ m + 1 by omega)
      simpa using this
    push_cast [Nat.cast_sub (by omega : 2 ^ (0 + 1) - 1 ≤ 2 ^ (m + 1) - 1),
      Nat.cast_sub (by norm_num : 1 ≤ 2 ^ (0 + 1)),
      Nat.cast_sub (by omega : 1 ≤ 2 ^ (m + 1))]
    norm_num
    ring
  rw [hz] at h
  have hcast : ((-(2 * (2 ^ (m + 1) - 1 : ℤ)) : ℤ) : ZMod (2 ^ (m + 3) - 4))
      = sheet m := by
    have h2 : ((2 * (2 ^ (m + 1) - 1) : ℕ) : ℤ) = 2 * (2 ^ (m + 1) - 1 : ℤ) := by
      have hp1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
      push_cast [Nat.cast_sub hp1]
      ring
    rw [← h2, Int.cast_neg, Int.cast_natCast, ← sheet]
    have h3 := two_nsmul_sheet m
    rw [two_nsmul] at h3
    exact neg_eq_of_add_eq_zero_right h3
  rw [hcast] at h
  apply pair_sum_eq_zero_of_ne (hβ _) (hβ _) (two_nsmul_sheet m)
  intro heq
  apply h
  rw [heq, ← two_nsmul]
  exact two_nsmul_sheet m

end Pins

section Closer

variable {m : ℕ} {g β : Fin (m + 3) → ZMod (2 ^ (m + 3) - 4)}

/-- Integer sum of the tail coins. -/
lemma sum_tau_int (m : ℕ) :
    ∑ j : Fin m, ((2 ^ (m + 1) - 1 - (2 ^ (j.val + 1) - 1) : ℕ) : ℤ)
      = m * (2 ^ (m + 1) - 1 : ℤ) - (2 ^ (m + 1) - 2 - m : ℤ) := by
  have hterm : ∀ j : Fin m,
      ((2 ^ (m + 1) - 1 - (2 ^ (j.val + 1) - 1) : ℕ) : ℤ)
        = (2 ^ (m + 1) - 1 : ℤ) - ((2 ^ (j.val + 1) - 1 : ℕ) : ℤ) := by
    intro j
    have hb : 2 ^ (j.val + 1) ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
    push_cast [Nat.cast_sub (Nat.sub_le_sub_right hb 1),
      Nat.cast_sub (Nat.one_le_pow _ _ (show 0 < 2 by norm_num) :
        1 ≤ 2 ^ (j.val + 1)), Nat.cast_sub h1]
    ring
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_sum,
      sum_pow_sub_one m, nsmul_eq_mul]
  have hm1 : m + 1 < 2 ^ (m + 1) := Nat.lt_two_pow_self
  have hc1 : (2 ^ (m + 1) - 2 - m : ℕ) = 2 ^ (m + 1) - (2 + m) := by omega
  rw [hc1, Nat.cast_sub (by omega : 2 + m ≤ 2 ^ (m + 1))]
  push_cast
  ring

/-- Integer sum of the whole parent. -/
lemma sum_rliftParent_int (m : ℕ) :
    ∑ i : Fin (m + 3), ((rliftParent m i : ℕ) : ℤ)
      = 1 + (m * (2 ^ (m + 1) - 1 : ℤ) - (2 ^ (m + 1) - 2 - m : ℤ))
        + 2 ^ (m + 1) := by
  have hcomp : (fun i : Fin (m + 3) => ((rliftParent m i : ℕ) : ℤ))
      = Fin.cons ((0 : ℕ) : ℤ) (Fin.cons ((1 : ℕ) : ℤ)
          (Fin.snoc
            (fun j : Fin m =>
              ((2 ^ (m + 1) - 1 - (2 ^ (j.val + 1) - 1) : ℕ) : ℤ))
            ((2 ^ (m + 1) : ℕ) : ℤ))) := by
    show (Nat.cast ∘ rliftParent m) = _
    rw [rliftParent, Fin.comp_cons, Fin.comp_cons, Fin.comp_snoc]
    rfl
  rw [hcomp, Fin.sum_cons, Fin.sum_cons, Fin.sum_snoc, sum_tau_int m]
  push_cast
  ring

/-- **The power chain closes.**  For even `m ≥ 2`, no lift of the
reflected child with an extra congruent to `2^(m+1)` modulo `2M` is a
valid tuple modulo `4M`. -/
theorem rliftParent_power_not_valid (hm2 : 2 ≤ m) (hme : Even m)
    (hβ : ∀ i, β i = 0 ∨ β i = sheet m)
    (hg : ∀ i, g i = ((rliftParent m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  haveI : NeZero m := ⟨by omega⟩
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet m
  have hE2 : 2 • β (extraC m) = 0 := hβ2 _
  -- the three pins, rearranged
  have htop : β ⟨0, by omega⟩ = sheet m + β (extraC m) :=
    eq_add_of_pair_sum hE2 (top_pin (by omega) hβ hg hv)
  have htau0 : β (tauC m 0 (by omega)) = β (extraC m) :=
    eq_of_pair_sum_zero hE2 (bottom_pin (by omega) hβ hg hv)
  have htauS : ∀ (j : ℕ) (hj : j + 1 < m),
      β (tauC m (j + 1) hj) = sheet m + β (extraC m) := fun j hj =>
    eq_add_of_pair_sum hE2 (chain_pin hβ hg hv j hj)
  -- the closing rival
  set ce : ℕ := if m % 4 = 0 then 3 else 1 with hce
  have hce13 : ce = 3 ∨ ce = 1 := by
    rw [hce]; split <;> simp
  have hce_le : ce ≤ 3 := by rcases hce13 with h | h <;> omega
  have hdvd : (4 : ℤ) ∣ ((ce : ℤ) + 1 - m) := by
    obtain ⟨m2, hm2'⟩ := hme
    have h4 : m % 4 = 0 ∨ m % 4 = 2 := by omega
    rcases h4 with h4 | h4
    · have : ce = 3 := by rw [hce, if_pos h4]
      rw [this]
      obtain ⟨m4, hm4⟩ := Nat.dvd_of_mod_eq_zero h4
      exact ⟨1 - m4, by rw [hm4]; push_cast; ring⟩
    · have : ce = 1 := by rw [hce, if_neg (by omega)]
      rw [this]
      have : m % 4 = 2 := h4
      obtain ⟨m4, hm4⟩ : ∃ t, m = 4 * t + 2 := ⟨m / 4, by omega⟩
      exact ⟨-m4, by rw [hm4]; push_cast; ring⟩
  have hone_ne_extra : (⟨1, by omega⟩ : Fin (m + 3)) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [extraC] at this
  set κ : Fin (m + 3) → ℕ := fun i =>
    if i = ⟨1, by omega⟩ then m + 2 - ce
    else if i = extraC m then ce + 1 else 0 with hκ
  have hκ1 : κ ⟨1, by omega⟩ = m + 2 - ce := by
    simp [hκ]
  have hκe : κ (extraC m) = ce + 1 := by
    simp only [hκ]
    rw [if_neg (Ne.symm hone_ne_extra)]
    simp
  have hκo : ∀ i, i ≠ ⟨1, by omega⟩ → i ≠ extraC m → κ i = 0 := by
    intro i h1 h2
    simp only [hκ]
    rw [if_neg h1, if_neg h2]
  have hκ0 : κ ⟨0, by omega⟩ = 0 := by
    apply hκo
    · intro h; have := congrArg Fin.val h; simp at this
    · intro h; have := congrArg Fin.val h; simp [extraC] at this
  have hκsum : ∑ i, κ i = m + 3 := by
    rw [sum_eq_of_two κ ⟨1, by omega⟩ (extraC m) hone_ne_extra hκo,
        hκ1, hκe]
    omega
  have hne := validTuple_no_shifted_rival hv κ hκsum (j := ⟨0, by omega⟩)
    (by rw [hκ0]; norm_num)
  rw [shifted_sum_eq (fun i => (κ i : ℤ) - 1) (rliftParent m) β g hβ2 hg] at hne
  -- the integer part
  have hint : ∑ i, ((κ i : ℤ) - 1) * (rliftParent m i : ℤ)
      = ((ce : ℤ) + 1 - m) * (2 ^ (m + 1) - 1) := by
    have hsplit : ∀ i : Fin (m + 3), ((κ i : ℤ) - 1) * (rliftParent m i : ℤ)
        = (κ i : ℤ) * (rliftParent m i : ℤ) - (rliftParent m i : ℤ) := by
      intro i; ring
    rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_sub_distrib,
        sum_rliftParent_int m]
    have hκr : ∑ i, (κ i : ℤ) * (rliftParent m i : ℤ)
        = ((m + 2 - ce : ℕ) : ℤ) * 1 + ((ce + 1 : ℕ) : ℤ) * 2 ^ (m + 1) := by
      rw [sum_eq_of_two (fun i => (κ i : ℤ) * (rliftParent m i : ℤ))
        ⟨1, by omega⟩ (extraC m) hone_ne_extra
        (by intro i h1 h2; simp [hκo i h1 h2])]
      rw [hκ1, hκe, rliftParent_one, rliftParent_last]
      push_cast
      ring
    rw [hκr, Nat.cast_sub (by omega : ce ≤ m + 2)]
    push_cast
    ring
  -- the bit part
  have hfe : Finset.univ.filter (fun i => Odd ((κ i : ℤ) - 1))
      = Finset.univ.erase ⟨1, by omega⟩ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · intro hodd heq
      subst heq
      rw [hκ1] at hodd
      have hcast : ((m + 2 - ce : ℕ) : ℤ) = (m : ℤ) + 2 - ce := by
        rw [Nat.cast_sub (by omega : ce ≤ m + 2)]; push_cast; ring
      rw [hcast] at hodd
      obtain ⟨m2, hm2'⟩ := hme
      rcases hce13 with h | h <;> rw [h] at hodd <;>
        · obtain ⟨w, hw⟩ := hodd
          omega
    · intro hne1
      by_cases he : i = extraC m
      · subst he
        rw [hκe]
        push_cast
        rcases hce13 with h | h <;> rw [h] <;> decide +kernel
      · rw [hκo i hne1 he]
        decide +kernel
  rw [hfe] at hne
  -- total bit sum vanishes
  have hτall : ∀ j : Fin m, β (tauC m j.val j.isLt)
      = if j = 0 then β (extraC m) else sheet m + β (extraC m) := by
    intro j
    by_cases hj0 : j = 0
    · subst hj0; simpa using htau0
    · have hjpos : 1 ≤ j.val := by
        rcases Nat.eq_zero_or_pos j.val with h | h
        · exact absurd (Fin.ext h) hj0
        · omega
      have hj1 : (j.val - 1) + 1 < m := by omega
      have hcoord : tauC m j.val j.isLt = tauC m ((j.val - 1) + 1) hj1 := by
        apply Fin.ext; simp [tauC]; omega
      rw [if_neg hj0, hcoord]
      exact htauS _ hj1
  have hτsum : ∑ j : Fin m, β (tauC m j.val j.isLt)
      = β (extraC m) + (m - 1) • (sheet m + β (extraC m)) := by
    rw [Finset.sum_congr rfl fun j _ => hτall j]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : Fin m))]
    rw [if_pos rfl]
    have herase : ∑ j ∈ Finset.univ.erase (0 : Fin m),
        (if j = 0 then β (extraC m) else sheet m + β (extraC m))
        = (m - 1) • (sheet m + β (extraC m)) := by
      rw [Finset.sum_congr rfl (fun j hj => if_neg (Finset.mem_erase.mp hj).1),
          Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
          Finset.card_univ, Fintype.card_fin]
    rw [herase]
    abel
  -- decompose the full bit sum by coordinates
  have hβdecomp : ∑ i, β i
      = β ⟨0, by omega⟩ + (β ⟨1, by omega⟩
        + ((∑ j : Fin m, β (tauC m j.val j.isLt)) + β (extraC m))) := by
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_castSucc]
    have h1 : Fin.succ (0 : Fin (m + 2)) = (⟨1, by omega⟩ : Fin (m + 3)) := by
      apply Fin.ext; simp
    have hτ : ∀ j : Fin m,
        Fin.succ (Fin.succ (Fin.castSucc j)) = tauC m j.val j.isLt := by
      intro j; apply Fin.ext; simp [tauC]
    have hlast : Fin.succ (Fin.succ (Fin.last m)) = extraC m := by
      apply Fin.ext; simp [extraC]
    have h0 : (0 : Fin (m + 3)) = ⟨0, by omega⟩ := rfl
    rw [h0, h1, hlast,
        Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => congrArg β (hτ j)]
  -- the erased bit sum vanishes
  have hbits : ∑ i ∈ Finset.univ.erase (⟨1, by omega⟩ : Fin (m + 3)), β i
      = 0 := by
    have hadd := Finset.sum_erase_add Finset.univ β
      (Finset.mem_univ (⟨1, by omega⟩ : Fin (m + 3)))
    rw [hβdecomp, htop, hτsum] at hadd
    have hmsmul : sheet m + β (extraC m)
        + ((β (extraC m) + (m - 1) • (sheet m + β (extraC m)))
          + β (extraC m))
        = m • (sheet m + β (extraC m)) := by
      have hsucc : m • (sheet m + β (extraC m))
          = (m - 1) • (sheet m + β (extraC m)) + (sheet m + β (extraC m)) := by
        rw [← succ_nsmul]
        congr 1
        omega
      rw [hsucc]
      have hEE : β (extraC m) + β (extraC m) = 0 := by
        rw [← two_nsmul]; exact hE2
      calc sheet m + β (extraC m)
          + ((β (extraC m) + (m - 1) • (sheet m + β (extraC m)))
            + β (extraC m))
          = (m - 1) • (sheet m + β (extraC m)) + (sheet m + β (extraC m))
            + (β (extraC m) + β (extraC m)) := by abel
        _ = (m - 1) • (sheet m + β (extraC m)) + (sheet m + β (extraC m)) := by
            rw [hEE, add_zero]
    have hzero : m • (sheet m + β (extraC m)) = 0 := by
      apply nsmul_eq_zero_of_even_of_two_nsmul_eq_zero _ hme
      rw [smul_add, two_nsmul_sheet m, hE2, add_zero]
    have hthis : ∑ i ∈ Finset.univ.erase (⟨1, by omega⟩ : Fin (m + 3)), β i
        + β ⟨1, by omega⟩ = β ⟨1, by omega⟩ := by
      rw [hadd,
        show sheet m + β (extraC m)
            + (β ⟨1, by omega⟩
              + ((β (extraC m) + (m - 1) • (sheet m + β (extraC m)))
                + β (extraC m)))
          = β ⟨1, by omega⟩ + (sheet m + β (extraC m)
              + ((β (extraC m) + (m - 1) • (sheet m + β (extraC m)))
                + β (extraC m))) from by abel,
        hmsmul, hzero, add_zero]
    have hthis' : ∑ i ∈ Finset.univ.erase (⟨1, by omega⟩ : Fin (m + 3)), β i
        + β ⟨1, by omega⟩ = 0 + β ⟨1, by omega⟩ := by
      rw [hthis, zero_add]
    exact add_right_cancel hthis'
  rw [hint, hbits, add_zero] at hne
  -- the chosen coefficient makes the integer part a multiple of the modulus
  apply hne
  obtain ⟨tq, htq⟩ := hdvd
  rw [htq]
  have hmod : ((4 : ℤ) * tq) * (2 ^ (m + 1) - 1)
      = tq * ((2 ^ (m + 3) - 4 : ℕ) : ℤ) := by
    have h1 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
    have := rlift_modulus m
    push_cast [Nat.cast_sub (by omega : 4 ≤ 2 ^ (m + 3))]
    have hp : ((2 : ℤ)) ^ (m + 3) = 4 * 2 ^ (m + 1) := by ring
    rw [hp]
    ring
  rw [hmod, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, mul_zero]

end Closer

end MinModulus
