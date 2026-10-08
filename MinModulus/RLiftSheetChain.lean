import MinModulus.RLiftBits
import MinModulus.RLiftPowerChain

/-!
# The sheet chain: reflected lifts with extra `≡ 1 (mod 2M)` are invalid

Setting: `m ≥ 2` even, `M = 2^(m+1) - 1`, parent modulus `N = 4M`.
The parent tuple `g` has `m + 3` coordinates: the first `m + 2` lift the
reflected child `(0, 1, M-1, M-3, …, M-(2^m - 1))` from `ZMod 2M` (one
free sheet bit each), and the last is the extra, here congruent to `1`
modulo `2M`.

This file proves such a parent is never a valid tuple, by the sheet
chain: the swap rival `e - u`, the telescope rivals on the exact
identity `2 τ_a + τ_{a+1} - τ_{a+2} = 2M + 2` (the top one landing on
the zero coin), and two bottom anchors force the `m + 1` sheet-bit
equations whose supports cancel while their targets sum to `sheet`.
-/

namespace MinModulus

open Finset

/-! ## Small-support sum helpers -/

section Sums

variable {n : ℕ} {A : Type*} [AddCommMonoid A]

/-- Splitting a sum at two distinguished points. -/
lemma sum_split_two (f : Fin n → A) (p q : Fin n) (hpq : p ≠ q) :
    ∑ i, f i = f p + f q + ∑ i ∈ Finset.univ \ {p, q}, f i := by
  classical
  have hsub : ({p, q} : Finset (Fin n)) ⊆ Finset.univ := Finset.subset_univ _
  rw [← Finset.sum_sdiff hsub, Finset.sum_insert (by simp [hpq]),
      Finset.sum_singleton]
  abel

/-- Sum of a function supported on at most four points. -/
lemma sum_eq_of_four (f : Fin n → A) (p q s t : Fin n)
    (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t)
    (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t)
    (h : ∀ i, i ≠ p → i ≠ q → i ≠ s → i ≠ t → f i = 0) :
    ∑ i, f i = f p + f q + f s + f t := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ ({p, q, s, t} : Finset (Fin n)))]
  · rw [Finset.sum_insert (by simp [hpq, hps, hpt]),
        Finset.sum_insert (by simp [hqs, hqt]),
        Finset.sum_insert (by simp [hst]), Finset.sum_singleton]
    abel
  · intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact h i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2

/-- Sum of a function supported on at most five points. -/
lemma sum_eq_of_five (f : Fin n → A) (p q s t u : Fin n)
    (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hpu : p ≠ u)
    (hqs : q ≠ s) (hqt : q ≠ t) (hqu : q ≠ u)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (h : ∀ i, i ≠ p → i ≠ q → i ≠ s → i ≠ t → i ≠ u → f i = 0) :
    ∑ i, f i = f p + f q + f s + f t + f u := by
  classical
  rw [← Finset.sum_subset
    (Finset.subset_univ ({p, q, s, t, u} : Finset (Fin n)))]
  · rw [Finset.sum_insert (by simp [hpq, hps, hpt, hpu]),
        Finset.sum_insert (by simp [hqs, hqt, hqu]),
        Finset.sum_insert (by simp [hst, hsu]),
        Finset.sum_insert (by simp [htu]), Finset.sum_singleton]
    abel
  · intro i _ hi
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
    exact h i hi.1 hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2

/-- Splitting a sum at five distinguished points. -/
lemma sum_split_five (f : Fin n → A) (p q s t u : Fin n)
    (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t) (hpu : p ≠ u)
    (hqs : q ≠ s) (hqt : q ≠ t) (hqu : q ≠ u)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    ∑ i, f i = f p + f q + f s + f t + f u
      + ∑ i ∈ Finset.univ \ {p, q, s, t, u}, f i := by
  classical
  have hsub : ({p, q, s, t, u} : Finset (Fin n)) ⊆ Finset.univ :=
    Finset.subset_univ _
  rw [← Finset.sum_sdiff hsub, Finset.sum_insert (by simp [hpq, hps, hpt, hpu]),
      Finset.sum_insert (by simp [hqs, hqt, hqu]),
      Finset.sum_insert (by simp [hst, hsu]),
      Finset.sum_insert (by simp [htu]), Finset.sum_singleton]
  abel

end Sums

/-! ## Two-torsion quad algebra -/

/-- The sum of two `{0, H}` elements is again in `{0, H}`. -/
lemma pair_sum_cases {G : Type*} [AddCommGroup G] {H x y : G}
    (hx : x = 0 ∨ x = H) (hy : y = 0 ∨ y = H) (hH : 2 • H = 0) :
    x + y = 0 ∨ x + y = H := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · left; simp
  · right; simp
  · right; simp
  · left; rw [← two_nsmul]; exact hH

/-- The sum of four `{0, H}` elements is again in `{0, H}`. -/
lemma quad_sum_cases {G : Type*} [AddCommGroup G] {H x y z w : G}
    (hx : x = 0 ∨ x = H) (hy : y = 0 ∨ y = H)
    (hz : z = 0 ∨ z = H) (hw : w = 0 ∨ w = H) (hH : 2 • H = 0) :
    x + y + z + w = 0 ∨ x + y + z + w = H := by
  have h3 := pair_sum_cases (pair_sum_cases hx hy hH)
    (pair_sum_cases hz hw hH) hH
  rwa [show x + y + (z + w) = x + y + z + w from by abel] at h3

/-- A nonzero `{0, H}` quad sum is exactly `H`. -/
lemma quad_sum_eq_of_ne_zero {G : Type*} [AddCommGroup G] {H x y z w : G}
    (hx : x = 0 ∨ x = H) (hy : y = 0 ∨ y = H)
    (hz : z = 0 ∨ z = H) (hw : w = 0 ∨ w = H) (hH : 2 • H = 0)
    (hne : x + y + z + w ≠ 0) : x + y + z + w = H :=
  (quad_sum_cases hx hy hz hw hH).resolve_left hne

/-- A `{0, H}` quad sum that cannot cancel `H` is zero. -/
lemma quad_sum_eq_zero_of_add_ne_zero {G : Type*} [AddCommGroup G]
    {H x y z w : G}
    (hx : x = 0 ∨ x = H) (hy : y = 0 ∨ y = H)
    (hz : z = 0 ∨ z = H) (hw : w = 0 ∨ w = H) (hH : 2 • H = 0)
    (hne : H + (x + y + z + w) ≠ 0) : x + y + z + w = 0 := by
  rcases quad_sum_cases hx hy hz hw hH with h | h
  · exact h
  · exfalso; apply hne; rw [h, ← two_nsmul]; exact hH

/-! ## The sheet parent -/

/-- Integer representatives of the whole parent: the reflected child
followed by the extra `1`. -/
def rliftParentSheet (m : ℕ) : Fin (m + 3) → ℕ :=
  Fin.cons 0 (Fin.cons 1
    (Fin.snoc (fun j : Fin m => 2 ^ (m + 1) - 1 - (2 ^ (j.val + 1) - 1))
      1))

lemma rliftParentSheet_zero (m : ℕ) : rliftParentSheet m ⟨0, by omega⟩ = 0 := rfl

lemma rliftParentSheet_one (m : ℕ) : rliftParentSheet m ⟨1, by omega⟩ = 1 := rfl

lemma rliftParentSheet_tau (m : ℕ) (j : ℕ) (h : j < m) :
    rliftParentSheet m (tauC m j h)
      = 2 ^ (m + 1) - 1 - (2 ^ (j + 1) - 1) := by
  have h1 : (tauC m j h) = Fin.succ (Fin.succ ⟨j, by omega⟩) := by
    apply Fin.ext; simp [tauC, Fin.succ]
  rw [h1, rliftParentSheet, Fin.cons_succ, Fin.cons_succ]
  have h2 : (⟨j, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨j, h⟩ := by
    apply Fin.ext; simp
  rw [h2, Fin.snoc_castSucc]

lemma rliftParentSheet_last (m : ℕ) :
    rliftParentSheet m (extraC m) = 1 := by
  have h1 : extraC m = Fin.succ (Fin.succ (Fin.last m)) := by
    apply Fin.ext; simp [extraC, Fin.succ]
  rw [h1, rliftParentSheet, Fin.cons_succ, Fin.cons_succ, Fin.snoc_last]

/-! ## The two rival engines -/

/-- Swap rival `p ↦ 2, q ↦ 0`: by validity, its value — integer part
plus the two odd-coefficient bits — is nonzero. -/
lemma rival_swap_ne (m : ℕ)
    (g β : Fin (m + 3) → ZMod (2 ^ (m + 3) - 4))
    (hβ2 : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((rliftParentSheet m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i)
    (hv : ValidTuple g) (p q : Fin (m + 3)) (hpq : p ≠ q) :
    ((((rliftParentSheet m p : ℤ) - rliftParentSheet m q) : ℤ) :
        ZMod (2 ^ (m + 3) - 4)) + (β p + β q) ≠ 0 := by
  classical
  set κ : Fin (m + 3) → ℕ :=
    fun i => if i = p then 2 else if i = q then 0 else 1 with hκ
  have hκp : κ p = 2 := by simp [hκ]
  have hκq : κ q = 0 := by simp [hκ, Ne.symm hpq]
  have hκo : ∀ i, i ≠ p → i ≠ q → κ i = 1 := by
    intro i h1 h2; simp [hκ, h1, h2]
  have hκsum : ∑ i, κ i = m + 3 := by
    rw [sum_split_two κ p q hpq, hκp, hκq]
    have hrest : ∑ i ∈ Finset.univ \ {p, q}, κ i
        = (Finset.univ \ ({p, q} : Finset (Fin (m + 3)))).card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hi
      exact hκo i hi.2.1 hi.2.2
    have hc2 : ({p, q} : Finset (Fin (m + 3))).card = 2 := by
      rw [Finset.card_insert_of_notMem (by simp [hpq]), Finset.card_singleton]
    rw [hrest, Finset.card_sdiff, Finset.inter_univ, hc2, Finset.card_univ,
        Fintype.card_fin]
    omega
  have hne := validTuple_no_shifted_rival hv κ hκsum (j := q)
    (by rw [hκq]; norm_num)
  rw [shifted_sum_eq (fun i => (κ i : ℤ) - 1) (rliftParentSheet m) β g hβ2 hg]
    at hne
  have hints : ∑ i, ((κ i : ℤ) - 1) * (rliftParentSheet m i : ℤ)
      = (rliftParentSheet m p : ℤ) - rliftParentSheet m q := by
    rw [sum_eq_of_two (fun i => ((κ i : ℤ) - 1) * (rliftParentSheet m i : ℤ))
      p q hpq (by intro i h1 h2; simp [hκo i h1 h2])]
    rw [hκp, hκq]
    push_cast
    ring
  have hfilter : ∑ i ∈ Finset.univ.filter (fun i => Odd ((κ i : ℤ) - 1)), β i
      = β p + β q := by
    rw [Finset.sum_filter]
    rw [sum_eq_of_two (fun i => if Odd ((κ i : ℤ) - 1) then β i else 0)
      p q hpq (by intro i h1 h2; rw [hκo i h1 h2]; norm_num)]
    rw [hκp, hκq]
    norm_num
  rw [hints, hfilter] at hne
  exact fun h => hne (by rw [← h])

/-- Five-point rival `p ↦ 3, q ↦ 2, a, b, c ↦ 0`: by validity, its
value — integer part plus the four odd-coefficient bits — is nonzero. -/
lemma rival_five_ne (m : ℕ) (hm2 : 2 ≤ m)
    (g β : Fin (m + 3) → ZMod (2 ^ (m + 3) - 4))
    (hβ2 : ∀ i, 2 • β i = 0)
    (hg : ∀ i, g i = ((rliftParentSheet m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i)
    (hv : ValidTuple g) (p q a b c : Fin (m + 3))
    (hpq : p ≠ q) (hpa : p ≠ a) (hpb : p ≠ b) (hpc : p ≠ c)
    (hqa : q ≠ a) (hqb : q ≠ b) (hqc : q ≠ c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    (((2 * (rliftParentSheet m p : ℤ) + rliftParentSheet m q
        - rliftParentSheet m a - rliftParentSheet m b
        - rliftParentSheet m c) : ℤ) : ZMod (2 ^ (m + 3) - 4))
      + (β q + β a + β b + β c) ≠ 0 := by
  classical
  set κ : Fin (m + 3) → ℕ :=
    fun i => if i = p then 3 else if i = q then 2 else if i = a then 0
      else if i = b then 0 else if i = c then 0 else 1 with hκ
  have hκp : κ p = 3 := by simp [hκ]
  have hκq : κ q = 2 := by simp [hκ, Ne.symm hpq]
  have hκa : κ a = 0 := by simp [hκ, Ne.symm hpa, Ne.symm hqa]
  have hκb : κ b = 0 := by simp [hκ, Ne.symm hpb, Ne.symm hqb, Ne.symm hab]
  have hκc : κ c = 0 := by
    simp [hκ, Ne.symm hpc, Ne.symm hqc, Ne.symm hac, Ne.symm hbc]
  have hκo : ∀ i, i ≠ p → i ≠ q → i ≠ a → i ≠ b → i ≠ c → κ i = 1 := by
    intro i h1 h2 h3 h4 h5; simp [hκ, h1, h2, h3, h4, h5]
  have hκsum : ∑ i, κ i = m + 3 := by
    rw [sum_split_five κ p q a b c hpq hpa hpb hpc hqa hqb hqc hab hac hbc,
        hκp, hκq, hκa, hκb, hκc]
    have hrest : ∑ i ∈ Finset.univ \ {p, q, a, b, c}, κ i
        = (Finset.univ \ ({p, q, a, b, c} : Finset (Fin (m + 3)))).card := by
      rw [Finset.card_eq_sum_ones]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
        not_or] at hi
      exact hκo i hi.2.1 hi.2.2.1 hi.2.2.2.1 hi.2.2.2.2.1 hi.2.2.2.2.2
    have hc5 : ({p, q, a, b, c} : Finset (Fin (m + 3))).card = 5 := by
      rw [Finset.card_insert_of_notMem (by simp [hpq, hpa, hpb, hpc]),
          Finset.card_insert_of_notMem (by simp [hqa, hqb, hqc]),
          Finset.card_insert_of_notMem (by simp [hab, hac]),
          Finset.card_insert_of_notMem (by simp [hbc]),
          Finset.card_singleton]
    rw [hrest, Finset.card_sdiff, Finset.inter_univ, hc5, Finset.card_univ,
        Fintype.card_fin]
    omega
  have hne := validTuple_no_shifted_rival hv κ hκsum (j := a)
    (by rw [hκa]; norm_num)
  rw [shifted_sum_eq (fun i => (κ i : ℤ) - 1) (rliftParentSheet m) β g hβ2 hg]
    at hne
  have hints : ∑ i, ((κ i : ℤ) - 1) * (rliftParentSheet m i : ℤ)
      = 2 * (rliftParentSheet m p : ℤ) + rliftParentSheet m q
        - rliftParentSheet m a - rliftParentSheet m b
        - rliftParentSheet m c := by
    rw [sum_eq_of_five
      (fun i => ((κ i : ℤ) - 1) * (rliftParentSheet m i : ℤ))
      p q a b c hpq hpa hpb hpc hqa hqb hqc hab hac hbc (by
        intro i h1 h2 h3 h4 h5
        simp [hκo i h1 h2 h3 h4 h5])]
    rw [hκp, hκq, hκa, hκb, hκc]
    push_cast
    ring
  have hfilter : ∑ i ∈ Finset.univ.filter (fun i => Odd ((κ i : ℤ) - 1)), β i
      = β q + β a + β b + β c := by
    rw [Finset.sum_filter]
    rw [sum_eq_of_four (fun i => if Odd ((κ i : ℤ) - 1) then β i else 0)
      q a b c hqa hqb hqc hab hac hbc (by
        intro i h2 h3 h4 h5
        by_cases h1 : i = p
        · subst h1
          rw [hκp]
          norm_num
        · rw [hκo i h1 h2 h3 h4 h5]
          norm_num)]
    rw [hκq, hκa, hκb, hκc]
    norm_num
  rw [hints, hfilter] at hne
  exact fun h => hne (by rw [← h])

/-! ## The five pins -/

section Pins

variable {m : ℕ} {g β : Fin (m + 3) → ZMod (2 ^ (m + 3) - 4)}

/-- Swap pin: the extra is congruent to the unit coin, so their sheet
bits must differ. -/
lemma sheet_swap_pin (hβ : ∀ i, β i = 0 ∨ β i = sheet m)
    (hg : ∀ i, g i = ((rliftParentSheet m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i)
    (hv : ValidTuple g) :
    β ⟨1, by omega⟩ + β (extraC m) = sheet m := by
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet m
  have hd : (⟨1, by omega⟩ : Fin (m + 3)) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [extraC] at this
  have h := rival_swap_ne m g β hβ2 hg hv _ _ hd
  rw [rliftParentSheet_one, rliftParentSheet_last] at h
  have hz : (((1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)) = 0 := by norm_num
  rw [hz] at h
  simp only [Int.cast_zero, zero_add] at h
  exact pair_sum_eq_of_ne_zero (hβ _) (hβ _) (two_nsmul_sheet m) h

/-- Telescope pin: the exact identity `2 τ_j + τ_{j+1} - τ_{j+2} = 2M + 2`
pins the four odd bits of the telescope rival to zero. -/
lemma sheet_telescope_pin (hm2 : 2 ≤ m)
    (hβ : ∀ i, β i = 0 ∨ β i = sheet m)
    (hg : ∀ i, g i = ((rliftParentSheet m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i)
    (hv : ValidTuple g) (j : ℕ) (hj : j + 2 < m) :
    β (tauC m (j + 1) (by omega)) + β ⟨1, by omega⟩
      + β (tauC m (j + 2) hj) + β (extraC m) = 0 := by
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet m
  have hd1 : tauC m j (by omega) ≠ tauC m (j + 1) (by omega) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd2 : tauC m j (by omega) ≠ (⟨1, by omega⟩ : Fin (m + 3)) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd3 : tauC m j (by omega) ≠ tauC m (j + 2) hj := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd4 : tauC m j (by omega) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this; omega
  have hd5 : tauC m (j + 1) (by omega) ≠ (⟨1, by omega⟩ : Fin (m + 3)) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd6 : tauC m (j + 1) (by omega) ≠ tauC m (j + 2) hj := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd7 : tauC m (j + 1) (by omega) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this; omega
  have hd8 : (⟨1, by omega⟩ : Fin (m + 3)) ≠ tauC m (j + 2) hj := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd9 : (⟨1, by omega⟩ : Fin (m + 3)) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [extraC] at this
  have hd10 : tauC m (j + 2) hj ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this; omega
  have h := rival_five_ne m hm2 g β hβ2 hg hv
    (tauC m j (by omega)) (tauC m (j + 1) (by omega))
    (⟨1, by omega⟩) (tauC m (j + 2) hj) (extraC m)
    hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10
  rw [rliftParentSheet_tau m j (by omega),
      rliftParentSheet_tau m (j + 1) (by omega),
      rliftParentSheet_tau m (j + 2) hj,
      rliftParentSheet_one, rliftParentSheet_last] at h
  have hz : (2 * ((2 ^ (m + 1) - 1 - (2 ^ (j + 1) - 1) : ℕ) : ℤ)
      + ((2 ^ (m + 1) - 1 - (2 ^ (j + 1 + 1) - 1) : ℕ) : ℤ)
      - ((1 : ℕ) : ℤ)
      - ((2 ^ (m + 1) - 1 - (2 ^ (j + 2 + 1) - 1) : ℕ) : ℤ)
      - ((1 : ℕ) : ℤ))
      = ((2 * (2 ^ (m + 1) - 1) : ℕ) : ℤ) := by
    have hb1 : 2 ^ (j + 1) ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb2 : 2 ^ (j + 1 + 1) ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb3 : 2 ^ (j + 2 + 1) ≤ 2 ^ (m + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hp1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hp2 : 1 ≤ 2 ^ (j + 1 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hp3 : 1 ≤ 2 ^ (j + 2 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hp4 : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by norm_num)
    push_cast [Nat.cast_sub (by omega : 2 ^ (j + 1) - 1 ≤ 2 ^ (m + 1) - 1),
      Nat.cast_sub (by omega : 2 ^ (j + 1 + 1) - 1 ≤ 2 ^ (m + 1) - 1),
      Nat.cast_sub (by omega : 2 ^ (j + 2 + 1) - 1 ≤ 2 ^ (m + 1) - 1),
      Nat.cast_sub hp1, Nat.cast_sub hp2, Nat.cast_sub hp3, Nat.cast_sub hp4]
    ring
  rw [hz] at h
  rw [Int.cast_natCast] at h
  have hs : ((2 * (2 ^ (m + 1) - 1) : ℕ) : ZMod (2 ^ (m + 3) - 4))
      = sheet m := rfl
  rw [hs] at h
  exact quad_sum_eq_zero_of_add_ne_zero (hβ _) (hβ _) (hβ _) (hβ _)
    (two_nsmul_sheet m) h

/-- Top pin: at the top of the chain the identity lands on the zero
coin, `2 τ_{m-2} + τ_{m-1} = 2M + 2`. -/
lemma sheet_top_pin (hm2 : 2 ≤ m)
    (hβ : ∀ i, β i = 0 ∨ β i = sheet m)
    (hg : ∀ i, g i = ((rliftParentSheet m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i)
    (hv : ValidTuple g) (j : ℕ) (hj : j + 2 = m) :
    β (tauC m (j + 1) (by omega)) + β ⟨0, by omega⟩
      + β ⟨1, by omega⟩ + β (extraC m) = 0 := by
  subst hj
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hd1 : tauC (j + 2) j (by omega) ≠ tauC (j + 2) (j + 1) (by omega) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd2 : tauC (j + 2) j (by omega) ≠ (⟨0, by omega⟩ : Fin (j + 2 + 3)) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd3 : tauC (j + 2) j (by omega) ≠ (⟨1, by omega⟩ : Fin (j + 2 + 3)) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd4 : tauC (j + 2) j (by omega) ≠ extraC (j + 2) := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this
  have hd5 : tauC (j + 2) (j + 1) (by omega)
      ≠ (⟨0, by omega⟩ : Fin (j + 2 + 3)) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd6 : tauC (j + 2) (j + 1) (by omega)
      ≠ (⟨1, by omega⟩ : Fin (j + 2 + 3)) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd7 : tauC (j + 2) (j + 1) (by omega) ≠ extraC (j + 2) := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this
  have hd8 : (⟨0, by omega⟩ : Fin (j + 2 + 3))
      ≠ (⟨1, by omega⟩ : Fin (j + 2 + 3)) := by
    intro h; have := congrArg Fin.val h; simp at this
  have hd9 : (⟨0, by omega⟩ : Fin (j + 2 + 3)) ≠ extraC (j + 2) := by
    intro h; have := congrArg Fin.val h; simp [extraC] at this
  have hd10 : (⟨1, by omega⟩ : Fin (j + 2 + 3)) ≠ extraC (j + 2) := by
    intro h; have := congrArg Fin.val h; simp [extraC] at this
  have h := rival_five_ne (j + 2) hm2 g β hβ2 hg hv
    (tauC (j + 2) j (by omega)) (tauC (j + 2) (j + 1) (by omega))
    (⟨0, by omega⟩) (⟨1, by omega⟩) (extraC (j + 2))
    hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10
  rw [rliftParentSheet_tau (j + 2) j (by omega),
      rliftParentSheet_tau (j + 2) (j + 1) (by omega),
      rliftParentSheet_zero, rliftParentSheet_one,
      rliftParentSheet_last] at h
  have hz : (2 * ((2 ^ (j + 2 + 1) - 1 - (2 ^ (j + 1) - 1) : ℕ) : ℤ)
      + ((2 ^ (j + 2 + 1) - 1 - (2 ^ (j + 1 + 1) - 1) : ℕ) : ℤ)
      - ((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ) - ((1 : ℕ) : ℤ))
      = ((2 * (2 ^ (j + 2 + 1) - 1) : ℕ) : ℤ) := by
    have hb1 : 2 ^ (j + 1) ≤ 2 ^ (j + 2 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hb2 : 2 ^ (j + 1 + 1) ≤ 2 ^ (j + 2 + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hp1 : 1 ≤ 2 ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hp2 : 1 ≤ 2 ^ (j + 1 + 1) := Nat.one_le_pow _ _ (by norm_num)
    have hp4 : 1 ≤ 2 ^ (j + 2 + 1) := Nat.one_le_pow _ _ (by norm_num)
    push_cast [Nat.cast_sub
      (by omega : 2 ^ (j + 1) - 1 ≤ 2 ^ (j + 2 + 1) - 1),
      Nat.cast_sub (by omega : 2 ^ (j + 1 + 1) - 1 ≤ 2 ^ (j + 2 + 1) - 1),
      Nat.cast_sub hp1, Nat.cast_sub hp2, Nat.cast_sub hp4]
    ring
  rw [hz] at h
  rw [Int.cast_natCast] at h
  have hs : ((2 * (2 ^ (j + 2 + 1) - 1) : ℕ) : ZMod (2 ^ (j + 2 + 3) - 4))
      = sheet (j + 2) := rfl
  rw [hs] at h
  exact quad_sum_eq_zero_of_add_ne_zero (hβ _) (hβ _) (hβ _) (hβ _)
    (two_nsmul_sheet _) h

/-- First bottom anchor: `2 τ_{m-1} = 2M + 2 - 2 τ_0 …` concretely,
`2 τ_{m-1} - 1 - τ_0 - 1 = 0`, pinning the zero coin, the unit coin,
the first tail coin and the extra. -/
lemma sheet_b1_pin (hm2 : 2 ≤ m)
    (hβ : ∀ i, β i = 0 ∨ β i = sheet m)
    (hg : ∀ i, g i = ((rliftParentSheet m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i)
    (hv : ValidTuple g) (j : ℕ) (hj : j + 1 = m) :
    β ⟨0, by omega⟩ + β ⟨1, by omega⟩
      + β (tauC m 0 (by omega)) + β (extraC m) = sheet m := by
  subst hj
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet _
  have hj1 : 1 ≤ j := by omega
  have hd1 : tauC (j + 1) j (by omega) ≠ (⟨0, by omega⟩ : Fin (j + 1 + 3)) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd2 : tauC (j + 1) j (by omega) ≠ (⟨1, by omega⟩ : Fin (j + 1 + 3)) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd3 : tauC (j + 1) j (by omega) ≠ tauC (j + 1) 0 (by omega) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this; omega
  have hd4 : tauC (j + 1) j (by omega) ≠ extraC (j + 1) := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this
  have hd5 : (⟨0, by omega⟩ : Fin (j + 1 + 3))
      ≠ (⟨1, by omega⟩ : Fin (j + 1 + 3)) := by
    intro h; have := congrArg Fin.val h; simp at this
  have hd6 : (⟨0, by omega⟩ : Fin (j + 1 + 3)) ≠ tauC (j + 1) 0 (by omega) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd7 : (⟨0, by omega⟩ : Fin (j + 1 + 3)) ≠ extraC (j + 1) := by
    intro h; have := congrArg Fin.val h; simp [extraC] at this
  have hd8 : (⟨1, by omega⟩ : Fin (j + 1 + 3)) ≠ tauC (j + 1) 0 (by omega) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd9 : (⟨1, by omega⟩ : Fin (j + 1 + 3)) ≠ extraC (j + 1) := by
    intro h; have := congrArg Fin.val h; simp [extraC] at this
  have hd10 : tauC (j + 1) 0 (by omega) ≠ extraC (j + 1) := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this
  have h := rival_five_ne (j + 1) hm2 g β hβ2 hg hv
    (tauC (j + 1) j (by omega)) (⟨0, by omega⟩) (⟨1, by omega⟩)
    (tauC (j + 1) 0 (by omega)) (extraC (j + 1))
    hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10
  rw [rliftParentSheet_tau (j + 1) j (by omega),
      rliftParentSheet_tau (j + 1) 0 (by omega),
      rliftParentSheet_zero, rliftParentSheet_one,
      rliftParentSheet_last] at h
  have hz : (2 * ((2 ^ (j + 1 + 1) - 1 - (2 ^ (j + 1) - 1) : ℕ) : ℤ)
      + ((0 : ℕ) : ℤ) - ((1 : ℕ) : ℤ)
      - ((2 ^ (j + 1 + 1) - 1 - (2 ^ (0 + 1) - 1) : ℕ) : ℤ)
      - ((1 : ℕ) : ℤ)) = 0 := by
    have hdbl : (2 : ℕ) ^ (j + 1 + 1) = 2 * 2 ^ (j + 1) := by ring
    have hp1 : 1 ≤ (2 : ℕ) ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
    have h01 : (2 : ℕ) ^ (0 + 1) = 2 := by norm_num
    have hA : (2 ^ (j + 1 + 1) - 1 - (2 ^ (j + 1) - 1) : ℕ)
        = 2 ^ (j + 1) := by omega
    have hB : (2 ^ (j + 1 + 1) - 1 - (2 ^ (0 + 1) - 1) : ℕ)
        = 2 * 2 ^ (j + 1) - 2 := by omega
    rw [hA, hB]
    push_cast [Nat.cast_sub (by omega : (2 : ℕ) ≤ 2 * 2 ^ (j + 1))]
    ring
  rw [hz] at h
  simp only [Int.cast_zero, zero_add] at h
  exact quad_sum_eq_of_ne_zero (hβ _) (hβ _) (hβ _) (hβ _)
    (two_nsmul_sheet _) h

/-- Second bottom anchor: `τ_0 - τ_1 = 2`, pinning the first two tail
coins, the unit coin and the extra. -/
lemma sheet_b2_pin (hm2 : 2 ≤ m)
    (hβ : ∀ i, β i = 0 ∨ β i = sheet m)
    (hg : ∀ i, g i = ((rliftParentSheet m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i)
    (hv : ValidTuple g) :
    β (tauC m 0 (by omega)) + β ⟨1, by omega⟩
      + β (tauC m 1 (by omega)) + β (extraC m) = sheet m := by
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet m
  have hd1 : (⟨0, by omega⟩ : Fin (m + 3)) ≠ tauC m 0 (by omega) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd2 : (⟨0, by omega⟩ : Fin (m + 3)) ≠ (⟨1, by omega⟩ : Fin (m + 3)) := by
    intro h; have := congrArg Fin.val h; simp at this
  have hd3 : (⟨0, by omega⟩ : Fin (m + 3)) ≠ tauC m 1 (by omega) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd4 : (⟨0, by omega⟩ : Fin (m + 3)) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [extraC] at this
  have hd5 : tauC m 0 (by omega) ≠ (⟨1, by omega⟩ : Fin (m + 3)) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd6 : tauC m 0 (by omega) ≠ tauC m 1 (by omega) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd7 : tauC m 0 (by omega) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this; omega
  have hd8 : (⟨1, by omega⟩ : Fin (m + 3)) ≠ tauC m 1 (by omega) := by
    intro h; have := congrArg Fin.val h; simp [tauC] at this
  have hd9 : (⟨1, by omega⟩ : Fin (m + 3)) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [extraC] at this
  have hd10 : tauC m 1 (by omega) ≠ extraC m := by
    intro h; have := congrArg Fin.val h; simp [tauC, extraC] at this; omega
  have h := rival_five_ne m hm2 g β hβ2 hg hv
    (⟨0, by omega⟩) (tauC m 0 (by omega)) (⟨1, by omega⟩)
    (tauC m 1 (by omega)) (extraC m)
    hd1 hd2 hd3 hd4 hd5 hd6 hd7 hd8 hd9 hd10
  rw [rliftParentSheet_tau m 0 (by omega), rliftParentSheet_tau m 1 (by omega),
      rliftParentSheet_zero, rliftParentSheet_one,
      rliftParentSheet_last] at h
  have hz : (2 * ((0 : ℕ) : ℤ)
      + ((2 ^ (m + 1) - 1 - (2 ^ (0 + 1) - 1) : ℕ) : ℤ)
      - ((1 : ℕ) : ℤ)
      - ((2 ^ (m + 1) - 1 - (2 ^ (1 + 1) - 1) : ℕ) : ℤ)
      - ((1 : ℕ) : ℤ)) = 0 := by
    have hb4 : (4 : ℕ) ≤ 2 ^ (m + 1) := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h01 : (2 : ℕ) ^ (0 + 1) = 2 := by norm_num
    have h11 : (2 : ℕ) ^ (1 + 1) = 4 := by norm_num
    have hA : (2 ^ (m + 1) - 1 - (2 ^ (0 + 1) - 1) : ℕ)
        = 2 ^ (m + 1) - 2 := by omega
    have hB : (2 ^ (m + 1) - 1 - (2 ^ (1 + 1) - 1) : ℕ)
        = 2 ^ (m + 1) - 4 := by omega
    rw [hA, hB]
    push_cast [Nat.cast_sub (by omega : (2 : ℕ) ≤ 2 ^ (m + 1)),
      Nat.cast_sub hb4]
    ring
  rw [hz] at h
  simp only [Int.cast_zero, zero_add] at h
  exact quad_sum_eq_of_ne_zero (hβ _) (hβ _) (hβ _) (hβ _)
    (two_nsmul_sheet m) h

end Pins

/-! ## Assembly -/

section Assembly

variable {m : ℕ} {g β : Fin (m + 3) → ZMod (2 ^ (m + 3) - 4)}

/-- **The sheet chain closes.**  For even `m ≥ 2`, no lift of the
reflected child with an extra congruent to `1` modulo `2M` is a valid
tuple modulo `4M`. -/
theorem rliftParentSheet_not_valid (hm2 : 2 ≤ m) (hme : Even m)
    (hβ : ∀ i, β i = 0 ∨ β i = sheet m)
    (hg : ∀ i, g i = ((rliftParentSheet m i : ℕ) : ZMod (2 ^ (m + 3) - 4)) + β i) :
    ¬ ValidTuple g := by
  intro hv
  have hβ2 : ∀ i, 2 • β i = 0 := by
    intro i
    rcases hβ i with h | h <;> rw [h]
    · simp
    · exact two_nsmul_sheet m
  have hUU : β ⟨1, by omega⟩ + β ⟨1, by omega⟩ = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have hEE : β (extraC m) + β (extraC m) = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  have h00 : β ⟨0, by omega⟩ + β ⟨0, by omega⟩ = 0 := by
    rw [← two_nsmul]; exact hβ2 _
  -- the swap pin
  have hswap : β ⟨1, by omega⟩ + β (extraC m) = sheet m :=
    sheet_swap_pin hβ hg hv
  -- telescope steps: adjacent tail bits (from index 1 on) differ by the sheet
  have hstep : ∀ (j : ℕ) (hjm : j + 2 < m),
      β (tauC m (j + 2) hjm) + β (tauC m (j + 1) (by omega)) = sheet m := by
    intro j hjm
    have hpin := sheet_telescope_pin hm2 hβ hg hv j hjm
    calc β (tauC m (j + 2) hjm) + β (tauC m (j + 1) (by omega))
        = (β (tauC m (j + 1) (by omega)) + β ⟨1, by omega⟩
            + β (tauC m (j + 2) hjm) + β (extraC m))
          + (β ⟨1, by omega⟩ + β (extraC m))
          - ((β ⟨1, by omega⟩ + β ⟨1, by omega⟩)
            + (β (extraC m) + β (extraC m))) := by abel
      _ = sheet m := by rw [hpin, hswap, hUU, hEE]; simp
  -- cross pin from the top and the first bottom anchor
  have hpin3 := sheet_top_pin hm2 hβ hg hv (m - 2) (by omega)
  have hpin4 := sheet_b1_pin hm2 hβ hg hv (m - 1) (by omega)
  have hcoord : tauC m (m - 2 + 1) (by omega) = tauC m (m - 1) (by omega) := by
    apply Fin.ext; simp [tauC]; omega
  rw [hcoord] at hpin3
  have hcross : β (tauC m 0 (by omega)) + β (tauC m (m - 1) (by omega))
      = sheet m := by
    calc β (tauC m 0 (by omega)) + β (tauC m (m - 1) (by omega))
        = (β (tauC m (m - 1) (by omega)) + β ⟨0, by omega⟩
            + β ⟨1, by omega⟩ + β (extraC m))
          + (β ⟨0, by omega⟩ + β ⟨1, by omega⟩
            + β (tauC m 0 (by omega)) + β (extraC m))
          - ((β ⟨0, by omega⟩ + β ⟨0, by omega⟩)
            + (β ⟨1, by omega⟩ + β ⟨1, by omega⟩)
            + (β (extraC m) + β (extraC m))) := by abel
      _ = sheet m := by rw [hpin3, hpin4, h00, hUU, hEE]; simp
  -- second bottom anchor: the first two tail bits agree
  have hpin5 := sheet_b2_pin hm2 hβ hg hv
  have ht01 : β (tauC m 0 (by omega)) + β (tauC m 1 (by omega)) = 0 := by
    calc β (tauC m 0 (by omega)) + β (tauC m 1 (by omega))
        = (β (tauC m 0 (by omega)) + β ⟨1, by omega⟩
            + β (tauC m 1 (by omega)) + β (extraC m))
          - (β ⟨1, by omega⟩ + β (extraC m)) := by abel
      _ = 0 := by rw [hpin5, hswap]; simp
  have ht10 : β (tauC m 1 (by omega)) = β (tauC m 0 (by omega)) :=
    (eq_of_pair_sum_zero (hβ2 _) ht01).symm
  -- the chain: every tail bit from index 1 up
  have hchain : ∀ (i : ℕ) (hi : i + 1 < m),
      β (tauC m (i + 1) (by omega)) = β (tauC m 1 (by omega)) + i • sheet m := by
    intro i
    induction i with
    | zero => intro hi; simp
    | succ i ih =>
      intro hi
      have hstep' : β (tauC m (i + 1 + 1) hi)
          + β (tauC m (i + 1) (by omega)) = sheet m := hstep i (by omega)
      have hih := ih (by omega)
      have hnext : β (tauC m (i + 1 + 1) hi)
          = sheet m + β (tauC m (i + 1) (by omega)) :=
        eq_add_of_pair_sum (hβ2 _) hstep'
      rw [hnext, hih, succ_nsmul]
      abel
  -- evaluate the chain at the top
  have hlast : β (tauC m (m - 1) (by omega))
      = β (tauC m 1 (by omega)) + (m - 2) • sheet m := by
    have h := hchain (m - 2) (by omega)
    have hcoord2 : tauC m (m - 2 + 1) (by omega) = tauC m (m - 1) (by omega) := by
      apply Fin.ext; simp [tauC]; omega
    rw [hcoord2] at h
    exact h
  have heven : (m - 2) • sheet m = 0 :=
    nsmul_eq_zero_of_even_of_two_nsmul_eq_zero (two_nsmul_sheet m) (by
      obtain ⟨t, ht⟩ := hme
      exact ⟨t - 1, by omega⟩)
  -- the contradiction
  have hfin : sheet m = 0 := by
    have h := hcross
    rw [hlast, ht10, heven, add_zero, ← two_nsmul, hβ2 _] at h
    exact h.symm
  exact sheet_ne_zero m hfin

end Assembly

end MinModulus
