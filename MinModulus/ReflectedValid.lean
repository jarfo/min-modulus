import MinModulus.GlobalRoadmap
import MinModulus.DigitLemmaR

/-!
# Even length validates the reflected family

For even `m` the reflected tuple
`R = (0, 1, M-1, M-3, …, M-(2^m - 1))` modulo `N = 2M`, `M = 2^(m+1)-1`,
is a valid tuple (`reflectedTupleE_valid_of_even`).

A hypothetical rival `k` gives the integer vector `w = k - 1` with
`∑ w = 0` and `N ∣ ∑ wᵢ rᵢ` for the integer representatives `r`.  Every
`rᵢ` except `r₁ = 1` is even, so `w₁` is even, hence `w₁ ≥ 0`.  The exact
integer identity `∑ wᵢ rᵢ = S·M - E` (with `S` the tail-coefficient sum
and `E = w₀ + ∑ⱼ w_{j+2} 2^(j+1)`) gives `M ∣ E`.  Shifting by the
all-ones vector, `f := e + 1 ≥ 0` on exponents `0..m` has
`∑ fᵢ 2^i = E + M = k'·M` and `∑ fᵢ = m + 1 - w₁`.  If `k' = 0` then
`w₁ = m + 1`, odd for even `m`, contradicting `2 ∣ w₁`.  If `k' ≥ 1` the
digit bound forces `∑ f = m + 1` and `w₁ = 0`, and its equality case
forces `k' = 1`, `f = 1`, i.e. `w = 0`: the rival is the all-ones vector.
-/

namespace MinModulus

open Finset

/-- The reflected tuple (same definition as `reflectedTuple`). -/
def reflectedTupleE (m : ℕ) : Fin (m + 2) → ZMod (2 ^ (m + 2) - 2) :=
  Fin.cons 0 (Fin.cons 1
    (fun j : Fin m => ((2 ^ (m + 1) - 1 : ℕ) : ZMod (2 ^ (m + 2) - 2))
      - ((2 ^ (j.val + 1) - 1 : ℕ) : ZMod (2 ^ (m + 2) - 2))))

/-- Integer representatives of the reflected tuple. -/
def reflectedInt (m : ℕ) : Fin (m + 2) → ℤ :=
  Fin.cons 0 (Fin.cons 1
    (fun j : Fin m => (2 ^ (m + 1) - 1) - (2 ^ (j.val + 1) - 1)))

lemma reflectedTupleE_eq_cast (m : ℕ) (i : Fin (m + 2)) :
    reflectedTupleE m i = ((reflectedInt m i : ℤ) : ZMod (2 ^ (m + 2) - 2)) := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [reflectedTupleE, reflectedInt]
  · refine Fin.cases ?_ (fun j => ?_) i
    · simp [reflectedTupleE, reflectedInt]
    · have h1 : (1 : ℕ) ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
      have h2 : (1 : ℕ) ≤ 2 ^ (j.val + 1) := Nat.one_le_pow _ _ (by norm_num)
      show reflectedTupleE m (Fin.succ (Fin.succ j)) = _
      simp only [reflectedTupleE, reflectedInt, Fin.cons_succ]
      push_cast [h1, h2]
      ring

/-- **Even length validates the reflected family.** -/
theorem reflectedTupleE_valid_of_even (m : ℕ) (heven : Even m) :
    ValidTuple (reflectedTupleE m) := by
  intro k hksum hkval
  set N := 2 ^ (m + 2) - 2 with hN
  have h1M : (1 : ℕ) ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
  have hNM : N = 2 * (2 ^ (m + 1) - 1) := by
    rw [hN, pow_succ 2 (m + 1)]
    omega
  haveI : NeZero N := ⟨by rw [hNM]; omega⟩
  set Mz : ℤ := 2 ^ (m + 1) - 1 with hMz
  have hNz : (N : ℤ) = 2 * Mz := by
    rw [hNM, hMz]
    push_cast [h1M]
    ring
  set w : Fin (m + 2) → ℤ := fun i => (k i : ℤ) - 1 with hw
  have hwlb : ∀ i, -1 ≤ w i := by
    intro i
    have h0 : (0 : ℤ) ≤ (k i : ℤ) := Int.natCast_nonneg _
    simp only [hw]
    omega
  have hs01 : (Fin.succ (0 : Fin (m + 1))) = (1 : Fin (m + 2)) := by
    apply Fin.ext
    simp
  have hwsum : ∑ i, w i = 0 := by
    simp only [hw]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    rw [← Nat.cast_sum, hksum]
    push_cast
    ring
  set S : ℤ := ∑ j : Fin m, w j.succ.succ with hS
  have hwsum' : w 0 + w 1 + S = 0 := by
    have h := hwsum
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hs01] at h
    rw [hS]
    linarith [h]
  -- divisibility of the weighted value
  have hzero : ∑ i, w i • reflectedTupleE m i = 0 := by
    have h1 : ∑ i, ((k i : ℤ)) • reflectedTupleE m i
        = ∑ i, ((1 : ℤ)) • reflectedTupleE m i := by
      have hl : ∀ i, ((k i : ℤ)) • reflectedTupleE m i
          = k i • reflectedTupleE m i := fun i => natCast_zsmul _ _
      rw [Finset.sum_congr rfl (fun i _ => hl i)]
      simpa using hkval
    calc ∑ i, w i • reflectedTupleE m i
        = ∑ i, (((k i : ℤ)) • reflectedTupleE m i
            - ((1 : ℤ)) • reflectedTupleE m i) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          simp only [hw]
          rw [sub_smul]
      _ = 0 := by rw [Finset.sum_sub_distrib, h1, sub_self]
  set V : ℤ := ∑ i, w i * reflectedInt m i with hV
  have hdvd : (N : ℤ) ∣ V := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hV]
    push_cast
    rw [← hzero]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [reflectedTupleE_eq_cast m i, zsmul_eq_mul]
  -- the exact integer identity V = S*M - E
  set T : ℤ := ∑ j : Fin m, w j.succ.succ * 2 ^ (j.val + 1) with hT
  set E : ℤ := w 0 + T with hE
  have hVexp : V = w 1 + (S * Mz - T + S) := by
    rw [hV, Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [reflectedInt, Fin.cons_zero, Fin.cons_succ]
    rw [hs01, hMz]
    have hterm : ∀ j : Fin m,
        w j.succ.succ * ((2 ^ (m + 1) - 1) - (2 ^ (j.val + 1) - 1))
          = w j.succ.succ * (2 ^ (m + 1) - 1)
            - w j.succ.succ * 2 ^ (j.val + 1) + w j.succ.succ := by
      intro j
      ring
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.sum_mul, ← hS, ← hT]
    ring
  have hVSE : V = S * Mz - E := by
    rw [hVexp, hE]
    linarith [hwsum']
  have hMdvdN : Mz ∣ (N : ℤ) := ⟨2, by rw [hNz]; ring⟩
  have hMdvdV : Mz ∣ V := dvd_trans hMdvdN hdvd
  have hMdvdE : Mz ∣ E := by
    have hEeq : E = S * Mz - V := by linarith [hVSE]
    rw [hEeq]
    exact dvd_sub (dvd_mul_left Mz S) hMdvdV
  -- parity of w 1
  have h2V : (2 : ℤ) ∣ V := dvd_trans ⟨Mz, hNz⟩ hdvd
  have h2tail : (2 : ℤ) ∣ (S * Mz - T + S) := by
    have hform : S * Mz - T + S
        = ∑ j : Fin m, w j.succ.succ * (2 ^ (m + 1) - 2 ^ (j.val + 1)) := by
      rw [hS, hT, hMz, Finset.sum_mul, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      ring
    rw [hform]
    refine Finset.dvd_sum (fun j _ => ?_)
    have hdiff : (2 : ℤ) ^ (m + 1) - 2 ^ (j.val + 1)
        = 2 * (2 ^ m - 2 ^ j.val) := by
      rw [pow_succ, pow_succ]
      ring
    rw [hdiff]
    exact Dvd.dvd.mul_left (dvd_mul_right 2 _) _
  have h2w1 : (2 : ℤ) ∣ w 1 := by
    have hwV : w 1 = V - (S * Mz - T + S) := by
      rw [hVexp]
      ring
    rw [hwV]
    exact dvd_sub h2V h2tail
  have hw1nn : 0 ≤ w 1 := by
    obtain ⟨t, ht⟩ := h2w1
    have := hwlb 1
    omega
  -- the shifted nonnegative vector and its window value
  set e : Fin (m + 1) → ℤ := Fin.cons (w 0) (fun j : Fin m => w j.succ.succ)
    with he
  have helb : ∀ i, -1 ≤ e i := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [he, Fin.cons_zero]
      exact hwlb 0
    · rw [he, Fin.cons_succ]
      exact hwlb _
  set f : Fin (m + 1) → ℕ := fun i => (e i + 1).toNat with hf
  have hfcast : ∀ i, (f i : ℤ) = e i + 1 := by
    intro i
    simp only [hf]
    exact Int.toNat_of_nonneg (by have := helb i; omega)
  have hesum : ∑ i, e i = w 0 + S := by
    rw [he, Fin.sum_cons, hS]
  have heval : ∑ i, e i * 2 ^ (i : ℕ) = E := by
    rw [Fin.sum_univ_succ]
    simp only [he, Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero,
      mul_one, Fin.val_succ]
    rw [hE, hT]
  have hpowz : ∑ i : Fin (m + 1), (2 : ℤ) ^ (i : ℕ) = Mz := by
    have hn := sum_pow_window (m + 1)
    have hc : ((∑ i : Fin (m + 1), 2 ^ (i : ℕ) : ℕ) : ℤ)
        = ((2 ^ (m + 1) - 1 : ℕ) : ℤ) := by
      rw [hn]
    push_cast [h1M] at hc
    rw [hMz]
    exact hc
  have hfval : ((∑ i, f i * 2 ^ (i : ℕ) : ℕ) : ℤ) = E + Mz := by
    push_cast
    have hterm : ∀ i : Fin (m + 1),
        ((f i : ℤ)) * 2 ^ (i : ℕ) = e i * 2 ^ (i : ℕ) + 2 ^ (i : ℕ) := by
      intro i
      rw [hfcast i]
      ring
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
        heval, hpowz]
  have hfsum : ((∑ i, f i : ℕ) : ℤ) = (m + 1 : ℤ) - w 1 := by
    push_cast
    have hterm : ∀ i : Fin (m + 1), ((f i : ℤ)) = e i + 1 := hfcast
    rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
        hesum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    push_cast
    linarith [hwsum']
  -- natural-number divisibility and the quotient k'
  have hMzc : Mz = ((2 ^ (m + 1) - 1 : ℕ) : ℤ) := by
    rw [hMz]
    push_cast [h1M]
    ring
  have hMdvdFz : Mz ∣ ((∑ i, f i * 2 ^ (i : ℕ) : ℕ) : ℤ) := by
    rw [hfval]
    exact dvd_add hMdvdE ⟨1, by ring⟩
  have hMdvdFn : (2 ^ (m + 1) - 1) ∣ (∑ i, f i * 2 ^ (i : ℕ)) := by
    rw [hMzc] at hMdvdFz
    exact_mod_cast hMdvdFz
  set k' : ℕ := (∑ i, f i * 2 ^ (i : ℕ)) / (2 ^ (m + 1) - 1) with hk'
  have hk'eq : ∑ i, f i * 2 ^ (i : ℕ) = k' * (2 ^ (m + 1) - 1) := by
    rw [hk', Nat.div_mul_cancel hMdvdFn]
  rcases Nat.eq_zero_or_pos k' with hk0 | hk1
  · -- k' = 0: the rival is "n copies of 1", impossible at even m
    exfalso
    rw [hk0, zero_mul] at hk'eq
    have hfle : ∑ i, f i ≤ ∑ i, f i * 2 ^ (i : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      calc f i = f i * 1 := (mul_one _).symm
      _ ≤ f i * 2 ^ (i : ℕ) :=
        Nat.mul_le_mul_left _ (Nat.one_le_pow _ _ (by norm_num))
    have hf0 : ∑ i, f i = 0 := by omega
    have hw1 : w 1 = (m + 1 : ℤ) := by
      have := hfsum
      rw [hf0] at this
      push_cast at this
      linarith
    obtain ⟨t, ht⟩ := heven
    obtain ⟨u, hu⟩ := h2w1
    rw [hw1] at hu
    have : (m : ℤ) = t + t := by exact_mod_cast ht
    omega
  · -- k' ≥ 1: digit bound and its equality case
    have hbd := digit_bound m (∑ i, f i) k' f hk1 rfl hk'eq
    have hfeq : ∑ i, f i = m + 1 := by
      have h1 := hfsum
      have h2 : ((∑ i, f i : ℕ) : ℤ) ≤ (m + 1 : ℤ) := by
        rw [h1]
        linarith [hw1nn]
      have h3 : ((m + 1 : ℕ) : ℤ) ≤ ((∑ i, f i : ℕ) : ℤ) := by
        exact_mod_cast hbd
      push_cast at h2 h3
      exact_mod_cast le_antisymm h2 (by exact_mod_cast h3)
    have hw10 : w 1 = 0 := by
      have h1 := hfsum
      rw [hfeq] at h1
      push_cast at h1
      linarith
    obtain ⟨hk'1, hfone⟩ := digit_eq m k' hk1 f hk'eq hfeq
    have hezero : ∀ i, e i = 0 := by
      intro i
      have h1 := hfcast i
      rw [hfone i] at h1
      push_cast at h1
      linarith
    have hwzero : ∀ i, w i = 0 := by
      intro i
      refine Fin.cases ?_ (fun i' => ?_) i
      · have := hezero 0
        rw [he, Fin.cons_zero] at this
        exact this
      · refine Fin.cases ?_ (fun j => ?_) i'
        · rw [hs01]
          exact hw10
        · have := hezero (Fin.succ j)
          rw [he, Fin.cons_succ] at this
          exact this
    intro i
    have := hwzero i
    simp only [hw] at this
    omega

end MinModulus
