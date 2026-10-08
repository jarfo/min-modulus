import Mathlib

/-!
# The digit lemma for Mersenne multiples in a bounded exponent window

`s2d` is the binary digit sum.  Main results (`digit_bound`, `digit_eq`):
any `f : Fin (m+1) → ℕ` with `∑ i, f i * 2^i = k * (2^(m+1) - 1)` and
`k ≥ 1` has `∑ i, f i ≥ m + 1`, and equality forces `k = 1`, `f = 1`.

Proof: carry-compression (`2·2^i → 2^(i+1)`, `i < m`) strictly lowers the
digit sum, so a minimal representation has `f i ≤ 1` below `m`; then
`f m = X / 2^m` and the low bits give `s2d (X % 2^m)`.  For `X = k·M` with
`k ≤ 2^m`, division gives `X / 2^m = 2k - 1` and `X % 2^m = 2^m - k`, and
the complement identity `s2d (2^m - k) = m - s2d (k-1)` with `s2d x ≤ x`
finishes: `(2k-1) + m - s2d (k-1) ≥ m + 1  ⟺  s2d (k-1) ≤ 2(k-1)`.
-/

namespace MinModulus

/-- Binary digit sum. -/
def s2d (x : ℕ) : ℕ := (Nat.digits 2 x).sum

lemma s2d_zero : s2d 0 = 0 := rfl

lemma s2d_bit (a b : ℕ) (hb : b ≤ 1) : s2d (2 * a + b) = s2d a + b := by
  rcases Nat.eq_zero_or_pos (2 * a + b) with h | h
  · have ha : a = 0 := by omega
    have hb0 : b = 0 := by omega
    simp [ha, hb0, s2d_zero]
  · unfold s2d
    rw [Nat.digits_def' (by norm_num : 1 < 2) h]
    have hmod : (2 * a + b) % 2 = b := by omega
    have hdiv : (2 * a + b) / 2 = a := by omega
    rw [hmod, hdiv, List.sum_cons]
    ring

lemma s2d_split (y : ℕ) : s2d y = s2d (y / 2) + y % 2 := by
  have h := s2d_bit (y / 2) (y % 2) (by omega)
  rwa [Nat.div_add_mod y 2] at h

lemma s2d_le (x : ℕ) : s2d x ≤ x := by
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    rcases Nat.eq_zero_or_pos x with h | h
    · simp [h, s2d_zero]
    · have := ih (x / 2) (by omega)
      have hs := s2d_split x
      omega

/-- Complement identity: for `y < 2^m`, `s2d (2^m - 1 - y) + s2d y = m`. -/
lemma s2d_compl (m : ℕ) : ∀ y, y < 2 ^ m → s2d (2 ^ m - 1 - y) + s2d y = m := by
  induction m with
  | zero => intro y hy; interval_cases y; simp [s2d_zero]
  | succ k ih =>
      intro y hy
      have hble : y % 2 ≤ 1 := by omega
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
      have hy'lt : y / 2 < 2 ^ k := by omega
      have hsplit : 2 ^ (k + 1) - 1 - y
          = 2 * (2 ^ k - 1 - y / 2) + (1 - y % 2) := by omega
      rw [hsplit, s2d_bit _ _ (by omega), s2d_split y]
      have := ih (y / 2) hy'lt
      omega

/-- A 0/1 vector's weighted binary value has digit sum equal to its sum. -/
lemma s2d_sum_bits (m : ℕ) : ∀ b : Fin m → ℕ, (∀ i, b i ≤ 1) →
    s2d (∑ i, b i * 2 ^ (i : ℕ)) = ∑ i, b i := by
  induction m with
  | zero => intro b _; simp [s2d_zero]
  | succ k ih =>
      intro b hb
      have key : ∀ i : Fin k,
          b i.succ * 2 ^ ((i.succ : Fin (k + 1)) : ℕ)
            = 2 * (b i.succ * 2 ^ (i : ℕ)) := by
        intro i
        rw [Fin.val_succ, pow_succ]
        ring
      rw [Fin.sum_univ_succ,
          Finset.sum_congr rfl (fun i _ => key i), ← Finset.mul_sum]
      simp only [Fin.val_zero, pow_zero, mul_one]
      rw [add_comm, s2d_bit _ _ (hb 0), ih _ (fun i => hb i.succ),
          Fin.sum_univ_succ]
      omega

/-- Sum of the full window of powers. -/
lemma sum_pow_window (m : ℕ) : ∑ i : Fin m, 2 ^ (i : ℕ) = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_last, Fin.val_castSucc]
      have h1 : 1 ≤ 2 ^ k := Nat.one_le_pow _ _ (by norm_num)
      have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
      omega

/-- Exact division of `a * 2^m + r` for `r < 2^m`. -/
lemma window_div (m a r : ℕ) (hr : r < 2 ^ m) :
    (a * 2 ^ m + r) / 2 ^ m = a ∧ (a * 2 ^ m + r) % 2 ^ m = r := by
  have hP : 0 < 2 ^ m := pow_pos (by norm_num : (0:ℕ) < 2) m
  constructor
  · rw [add_comm, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- The merge move: replacing two coins at position `i < m` by one at
`i + 1` preserves the value and lowers the digit sum by one. -/
lemma merge_move (m : ℕ) (f : Fin (m + 1) → ℕ) (i : Fin (m + 1))
    (him : (i : ℕ) < m) (hfi : 2 ≤ f i) :
    ∃ f' : Fin (m + 1) → ℕ,
      (∑ j, f' j) + 1 = ∑ j, f j ∧
      ∑ j, f' j * 2 ^ (j : ℕ) = ∑ j, f j * 2 ^ (j : ℕ) := by
  set i' : Fin (m + 1) := ⟨(i : ℕ) + 1, by omega⟩ with hi'
  have hne : i' ≠ i := Fin.ne_of_val_ne (show (i : ℕ) + 1 ≠ (i : ℕ) by omega)
  refine ⟨fun j => if j = i then f i - 2 else if j = i' then f i' + 1 else f j,
    ?_, ?_⟩
  · show (∑ j, if j = i then f i - 2 else if j = i' then f i' + 1 else f j) + 1
        = ∑ j, f j
    have hpt : ∀ j, (if j = i then f i - 2 else if j = i' then f i' + 1 else f j)
        + (if j = i then 2 else 0) = f j + (if j = i' then 1 else 0) := by
      intro j
      by_cases h1 : j = i
      · subst h1
        rw [if_pos rfl, if_pos rfl, if_neg (fun h => hne h.symm)]
        omega
      · by_cases h2 : j = i'
        · subst h2
          simp [h1]
        · simp [h1, h2]
    have := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hpt j)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ i (fun _ => 2),
        Finset.sum_ite_eq' Finset.univ i' (fun _ => 1)] at this
    simp only [Finset.mem_univ, if_true] at this
    omega
  · show (∑ j, (if j = i then f i - 2 else if j = i' then f i' + 1 else f j)
        * 2 ^ (j : ℕ)) = ∑ j, f j * 2 ^ (j : ℕ)
    have h2i : 2 ^ ((i' : Fin (m + 1)) : ℕ) = 2 * 2 ^ (i : ℕ) := by
      show (2 : ℕ) ^ ((i : ℕ) + 1) = 2 * 2 ^ (i : ℕ)
      rw [pow_succ]
      ring
    have hpt : ∀ j, (if j = i then f i - 2 else if j = i' then f i' + 1 else f j)
          * 2 ^ (j : ℕ) + (if j = i then 2 * 2 ^ (i : ℕ) else 0)
        = f j * 2 ^ (j : ℕ) + (if j = i' then 2 ^ ((i' : Fin (m+1)) : ℕ) else 0) := by
      intro j
      by_cases h1 : j = i
      · subst h1
        rw [if_pos rfl, if_pos rfl, if_neg (fun h => hne h.symm)]
        have hsm := Nat.sub_mul (f j) 2 (2 ^ (j : ℕ))
        have h2 : 2 * 2 ^ (j : ℕ) ≤ f j * 2 ^ (j : ℕ) :=
          Nat.mul_le_mul_right _ hfi
        omega
      · by_cases h2 : j = i'
        · subst h2
          simp [h1]
          ring
        · simp [h1, h2]
    have := Finset.sum_congr rfl (fun j (_ : j ∈ Finset.univ) => hpt j)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.sum_ite_eq' Finset.univ i (fun _ => 2 * 2 ^ (i : ℕ)),
        Finset.sum_ite_eq' Finset.univ i'
          (fun _ => 2 ^ ((i' : Fin (m+1)) : ℕ))] at this
    simp only [Finset.mem_univ, if_true] at this
    rw [h2i] at this
    omega


/-- **Digit bound.**  A window-`[0,m]` representation of a positive
multiple of `2^(m+1) - 1` has digit sum at least `m + 1`. -/
theorem digit_bound (m : ℕ) : ∀ s k (f : Fin (m + 1) → ℕ), 1 ≤ k →
    ∑ i, f i = s → ∑ i, f i * 2 ^ (i : ℕ) = k * (2 ^ (m + 1) - 1) →
    m + 1 ≤ s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro k f hk hs hV
    by_cases hmerge : ∃ i : Fin (m + 1), (i : ℕ) < m ∧ 2 ≤ f i
    · obtain ⟨i, him, hfi⟩ := hmerge
      obtain ⟨f', hsum', hval'⟩ := merge_move m f i him hfi
      have hs1 : 1 ≤ s := by
        rw [← hs]
        calc 1 ≤ f i := by omega
        _ ≤ ∑ j, f j := Finset.single_le_sum (fun j _ => Nat.zero_le _)
            (Finset.mem_univ i)
      have := ih (s - 1) (by omega) k f' hk (by omega) (hval'.trans hV)
      omega
    · have hle : ∀ i : Fin (m + 1), (i : ℕ) < m → f i ≤ 1 := by
        intro i hi
        by_contra h
        exact hmerge ⟨i, hi, by omega⟩
      set b : Fin m → ℕ := fun i => f i.castSucc with hbdef
      have hb : ∀ i, b i ≤ 1 := fun i => hle i.castSucc (by simp)
      have hsplit : ∑ i, f i = (∑ i : Fin m, b i) + f (Fin.last m) := by
        rw [Fin.sum_univ_castSucc]
      have hvsplit : ∑ i, f i * 2 ^ (i : ℕ)
          = (∑ i : Fin m, b i * 2 ^ (i : ℕ)) + f (Fin.last m) * 2 ^ m := by
        rw [Fin.sum_univ_castSucc]
        simp [hbdef, Fin.val_last]
      set r := ∑ i : Fin m, b i * 2 ^ (i : ℕ) with hrdef
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
      have hrlt : r < 2 ^ m := by
        have hle' : r ≤ ∑ i : Fin m, 2 ^ (i : ℕ) := by
          apply Finset.sum_le_sum
          intro i _
          calc b i * 2 ^ (i : ℕ) ≤ 1 * 2 ^ (i : ℕ) :=
                Nat.mul_le_mul_right _ (hb i)
          _ = 2 ^ (i : ℕ) := one_mul _
        rw [sum_pow_window] at hle'
        omega
      have hX : k * (2 ^ (m + 1) - 1) = f (Fin.last m) * 2 ^ m + r := by
        rw [← hV, hvsplit]
        omega
      rcases Nat.lt_or_ge (2 ^ m) k with hklarge | hksmall
      · -- huge k: the top coefficient alone exceeds m + 1
        have hMge : 2 ^ m ≤ 2 ^ (m + 1) - 1 := by
          have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
          omega
        have hXge : k * 2 ^ m ≤ k * (2 ^ (m + 1) - 1) :=
          Nat.mul_le_mul_left _ hMge
        have hFk : k ≤ f (Fin.last m) := by
          by_contra hF
          rw [Nat.not_le] at hF
          have hmul : f (Fin.last m) * 2 ^ m ≤ (k - 1) * 2 ^ m :=
            Nat.mul_le_mul_right _ (by omega)
          have hsm : (k - 1) * 2 ^ m = k * 2 ^ m - 2 ^ m := by
            rw [Nat.sub_mul, one_mul]
          have hle2 : 2 ^ m ≤ k * 2 ^ m :=
            Nat.le_mul_of_pos_left _ (by omega)
          omega
        have h2m : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
        have hsF : f (Fin.last m) ≤ s := by
          rw [← hs, hsplit]
          omega
        omega
      · -- main case: exact division at the window top
        have hdecomp : k * (2 ^ (m + 1) - 1)
            = (2 * k - 1) * 2 ^ m + (2 ^ m - k) := by
          zify [show (1:ℕ) ≤ 2 ^ (m + 1) from Nat.one_le_pow _ _ (by norm_num),
                hksmall, show (1:ℕ) ≤ 2 * k by omega]
          ring
        have hnum : f (Fin.last m) * 2 ^ m + r
            = (2 * k - 1) * 2 ^ m + (2 ^ m - k) := by omega
        have hdm := window_div m (f (Fin.last m)) r hrlt
        have hdm2 := window_div m (2 * k - 1) (2 ^ m - k) (by omega)
        have hF : f (Fin.last m) = 2 * k - 1 := by
          have e1 := hdm.1
          rw [hnum, hdm2.1] at e1
          omega
        have hr : r = 2 ^ m - k := by
          have e1 := hdm.2
          rw [hnum, hdm2.2] at e1
          omega
        have hs2r : s2d r = ∑ i : Fin m, b i := s2d_sum_bits m b hb
        have hcompl := s2d_compl m (k - 1) (by omega)
        have hrw : 2 ^ m - 1 - (k - 1) = 2 ^ m - k := by omega
        rw [hrw] at hcompl
        have hs2le := s2d_le (k - 1)
        have hbs2 : (∑ i : Fin m, b i) = s2d (2 ^ m - k) := by
          rw [← hs2r, hr]
        have hfin : m + 1 ≤ (∑ i : Fin m, b i) + f (Fin.last m) := by omega
        rw [← hs, hsplit]
        omega

/-- **Equality case of the digit bound**: digit sum exactly `m + 1` forces
`k = 1` and the all-ones representation. -/
theorem digit_eq (m k : ℕ) (hk : 1 ≤ k) (f : Fin (m + 1) → ℕ)
    (hV : ∑ i, f i * 2 ^ (i : ℕ) = k * (2 ^ (m + 1) - 1))
    (hs : ∑ i, f i = m + 1) : k = 1 ∧ ∀ i, f i = 1 := by
  have hmerge : ¬ ∃ i : Fin (m + 1), (i : ℕ) < m ∧ 2 ≤ f i := by
    rintro ⟨i, him, hfi⟩
    obtain ⟨f', hsum', hval'⟩ := merge_move m f i him hfi
    have := digit_bound m (∑ j, f' j) k f' hk rfl (hval'.trans hV)
    omega
  have hle : ∀ i : Fin (m + 1), (i : ℕ) < m → f i ≤ 1 := by
    intro i hi
    by_contra h
    exact hmerge ⟨i, hi, by omega⟩
  set b : Fin m → ℕ := fun i => f i.castSucc with hbdef
  have hb : ∀ i, b i ≤ 1 := fun i => hle i.castSucc (by simp)
  have hsplit : ∑ i, f i = (∑ i : Fin m, b i) + f (Fin.last m) := by
    rw [Fin.sum_univ_castSucc]
  have hvsplit : ∑ i, f i * 2 ^ (i : ℕ)
      = (∑ i : Fin m, b i * 2 ^ (i : ℕ)) + f (Fin.last m) * 2 ^ m := by
    rw [Fin.sum_univ_castSucc]
    simp [hbdef, Fin.val_last]
  set r := ∑ i : Fin m, b i * 2 ^ (i : ℕ) with hrdef
  have h1 : 1 ≤ 2 ^ m := Nat.one_le_pow _ _ (by norm_num)
  have hrlt : r < 2 ^ m := by
    have hle' : r ≤ ∑ i : Fin m, 2 ^ (i : ℕ) := by
      apply Finset.sum_le_sum
      intro i _
      calc b i * 2 ^ (i : ℕ) ≤ 1 * 2 ^ (i : ℕ) := Nat.mul_le_mul_right _ (hb i)
      _ = 2 ^ (i : ℕ) := one_mul _
    rw [sum_pow_window] at hle'
    omega
  have hX : k * (2 ^ (m + 1) - 1) = f (Fin.last m) * 2 ^ m + r := by
    rw [← hV, hvsplit]
    omega
  have hksmall : k ≤ 2 ^ m := by
    by_contra hklarge
    rw [Nat.not_le] at hklarge
    have hMge : 2 ^ m ≤ 2 ^ (m + 1) - 1 := by
      have hp : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
      omega
    have hXge : k * 2 ^ m ≤ k * (2 ^ (m + 1) - 1) := Nat.mul_le_mul_left _ hMge
    have hFk : k ≤ f (Fin.last m) := by
      by_contra hF
      rw [Nat.not_le] at hF
      have hmul : f (Fin.last m) * 2 ^ m ≤ (k - 1) * 2 ^ m :=
        Nat.mul_le_mul_right _ (by omega)
      have hsm : (k - 1) * 2 ^ m = k * 2 ^ m - 2 ^ m := by
        rw [Nat.sub_mul, one_mul]
      have hle2 : 2 ^ m ≤ k * 2 ^ m := Nat.le_mul_of_pos_left _ (by omega)
      omega
    have h2m : m + 1 ≤ 2 ^ m := Nat.lt_two_pow_self
    have hsF : f (Fin.last m) ≤ ∑ i, f i := by
      rw [hsplit]
      omega
    omega
  have hdecomp : k * (2 ^ (m + 1) - 1)
      = (2 * k - 1) * 2 ^ m + (2 ^ m - k) := by
    zify [show (1:ℕ) ≤ 2 ^ (m + 1) from Nat.one_le_pow _ _ (by norm_num),
          hksmall, show (1:ℕ) ≤ 2 * k by omega]
    ring
  have hnum : f (Fin.last m) * 2 ^ m + r
      = (2 * k - 1) * 2 ^ m + (2 ^ m - k) := by omega
  have hdm := window_div m (f (Fin.last m)) r hrlt
  have hdm2 := window_div m (2 * k - 1) (2 ^ m - k) (by omega)
  have hF : f (Fin.last m) = 2 * k - 1 := by
    have e1 := hdm.1
    rw [hnum, hdm2.1] at e1
    omega
  have hr : r = 2 ^ m - k := by
    have e1 := hdm.2
    rw [hnum, hdm2.2] at e1
    omega
  have hs2r : s2d r = ∑ i : Fin m, b i := s2d_sum_bits m b hb
  have hcompl := s2d_compl m (k - 1) (by omega)
  have hrw : 2 ^ m - 1 - (k - 1) = 2 ^ m - k := by omega
  rw [hrw] at hcompl
  have hs2le := s2d_le (k - 1)
  have hbs2 : (∑ i : Fin m, b i) = s2d (2 ^ m - k) := by
    rw [← hs2r, hr]
  have hk1 : k = 1 := by omega
  subst hk1
  have hF1 : f (Fin.last m) = 1 := by omega
  have hbsum : ∑ i : Fin m, b i = m := by omega
  have hball : ∀ i : Fin m, b i = 1 := by
    by_contra h
    obtain ⟨j, hj⟩ := not_forall.mp h
    have hlt : ∑ i : Fin m, b i < ∑ i : Fin m, 1 :=
      Finset.sum_lt_sum (fun i _ => hb i)
        ⟨j, Finset.mem_univ j, by have := hb j; omega⟩
    simp at hlt
    omega
  refine ⟨rfl, ?_⟩
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · exact hF1
  · exact hball j

end MinModulus
