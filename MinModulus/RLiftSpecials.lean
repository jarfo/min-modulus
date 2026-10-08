import MinModulus.RLiftMasterAssembly

/-!
# The three special certificates

The exceptional targets of the master coverage that do not fall to the
chain or grid families: `e ≡ 2 (mod M)`, `e ≡ 3·2^{m−1} (mod 2M)`, and the
sporadic `(m, e) = (9, 10)`.  Each is a `z₂`-shift pair built on a
four-coin reserve.
-/

set_option maxHeartbeats 1600000

namespace MinModulus

open Finset

/-- Geometric sum over `ℕ`. -/
lemma nat_geom_sum (n : ℕ) : ∑ i ∈ range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : (1 : ℕ) ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    rw [Finset.sum_range_succ, ih, pow_succ]
    omega

/-- The value formula with an arbitrary zero-coin coefficient. -/
lemma master_value_c0 (L e : ℕ) (c0 c1 ce : ℤ) (f : ℕ → ℕ) :
    ∑ i, masterCoeff L c0 c1 (fun j => (f j.val : ℤ) - 1) ce i
        * ((rliftParentE L e i : ℕ) : ℤ)
      = c1 + ((dsum L f : ℤ) - L) * 2 ^ (L + 1) - 2 * (val L f : ℤ)
        + (2 ^ (L + 1) - 2) + ce * e := by
  have h0 := master_value L e c1 ce f
  rw [masterCoeff_mul_sum] at h0 ⊢
  have hv0 : ((rliftParentE L e ⟨0, by omega⟩ : ℕ) : ℤ) = 0 := by
    rw [rliftParentE_zero]; simp
  rw [hv0] at h0 ⊢
  linear_combination h0

/-- Core theorem for the `z₂` shift: a coin family with a four-coin reserve
at exponent `a` (interior: `a + 1 < L`), coefficient sum zero and value a
multiple of `2M` yields the special rival pair. -/
theorem special_pair_not_valid_core (L e : ℕ) (f : ℕ → ℕ) (a : ℕ)
    (haL : a + 1 < L) (hfa : 4 ≤ f a) (c0 c1 ce : ℤ)
    (hc0 : -1 ≤ c0) (hc1 : -1 ≤ c1) (hcef : -1 ≤ ce) (hce0 : ce ≠ 0)
    (hF : c0 + c1 + ((dsum L f : ℤ) - L) + ce = 0)
    (hV : ∃ G : ℤ, c1 + ((dsum L f : ℤ) - L) * 2 ^ (L + 1)
          - 2 * (val L f : ℤ) + (2 ^ (L + 1) - 2) + ce * e
        = 2 * (2 ^ (L + 1) - 1) * G)
    {g β : Fin (L + 3) → ZMod (2 ^ (L + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet L)
    (hg : ∀ i, g i = ((rliftParentE L e i : ℕ) : ZMod (2 ^ (L + 3) - 4))
        + β i) :
    ¬ ValidTuple g := by
  intro hv
  set r : Fin (L + 3) → ℕ := rliftParentE L e with hr
  set d : Fin L → ℤ := fun j => (f j.val : ℤ) - 1 with hd
  set c : Fin (L + 3) → ℤ := masterCoeff L c0 c1 d ce with hc
  have haL' : a < L := by omega
  have ha1L : a + 1 < L := haL
  have hane : a ≠ a + 1 := by omega
  have hdsum : ∑ j : Fin L, d j = (dsum L f : ℤ) - L := by
    rw [hd]
    rw [Finset.sum_sub_distrib]
    have hf : ∑ j : Fin L, (f j.val : ℤ) = (dsum L f : ℤ) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (f i : ℤ)) L, dsum]
      push_cast
      rfl
    rw [hf, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    ring
  have hcsum : ∑ i, c i = 0 := by
    rw [hc, sum_masterCoeff, hdsum]
    linarith
  have hcfloor : ∀ i, -1 ≤ c i := by
    rw [hc]
    refine masterCoeff_floor L c0 c1 ce d hc0 hc1 ?_ hcef
    intro j
    have := Int.natCast_nonneg (f j.val)
    simp only [hd]
    omega
  have hclast : c (extraC L) = ce := by rw [hc, masterCoeff_last]
  -- the z₂ partner: −4 at τ_a, +2 at τ_{a+1}, +2 at the unit
  set d' : Fin L → ℤ := fun j =>
    d j + (if j.val = a then -4 else 0) + (if j.val = a + 1 then 2 else 0)
    with hd'
  set c' : Fin (L + 3) → ℤ := masterCoeff L c0 (c1 + 2) d' ce with hc'
  have hd'sum : ∑ j : Fin L, d' j = (∑ j : Fin L, d j) + -2 := by
    rw [hd']
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    have h1 := fin_sum_ite_mul L a haL' (-4) (fun _ => 1)
    have h2 := fin_sum_ite_mul L (a + 1) ha1L 2 (fun _ => 1)
    simp only [mul_one] at h1 h2
    rw [h1, h2]
    ring
  have hc'sum : ∑ i, c' i = 0 := by
    rw [hc', sum_masterCoeff, hd'sum, hdsum]
    linarith
  have hc'floor : ∀ i, -1 ≤ c' i := by
    rw [hc']
    refine masterCoeff_floor L c0 (c1 + 2) ce d' hc0 (by omega) ?_ hcef
    intro j
    have h0 := Int.natCast_nonneg (f j.val)
    simp only [hd', hd]
    by_cases hja : j.val = a
    · have hfj : (4 : ℤ) ≤ (f j.val : ℤ) := by
        have hfe : f j.val = f a := by rw [hja]
        rw [hfe]; exact_mod_cast hfa
      have hja1 : ¬ j.val = a + 1 := by omega
      simp only [if_pos hja, if_neg hja1]
      omega
    · by_cases hja1 : j.val = a + 1
      · simp only [if_neg hja, if_pos hja1]
        omega
      · simp only [if_neg hja, if_neg hja1]
        omega
  have hc'last : c' (extraC L) = ce := by rw [hc', masterCoeff_last]
  have hpar : ∀ i, Odd (c i) ↔ Odd (c' i) := by
    intro i
    refine odd_iff_of_even_diff ?_
    rw [hc, hc']
    refine masterCoeff_even_diff L c0 c0 c1 (c1 + 2) ce ce d d'
      ⟨0, by ring⟩ ⟨1, by ring⟩ ?_ ⟨0, by ring⟩ i
    intro j
    by_cases hja : j.val = a
    · have hja1 : ¬ j.val = a + 1 := by omega
      exact ⟨-2, by simp only [hd', if_pos hja, if_neg hja1]; ring⟩
    · by_cases hja1 : j.val = a + 1
      · exact ⟨1, by simp only [hd', if_neg hja, if_pos hja1]; ring⟩
      · exact ⟨0, by simp only [hd', if_neg hja, if_neg hja1]; ring⟩
  have hVc : ∑ i, c i * (r i : ℤ)
      = c1 + ((dsum L f : ℤ) - L) * 2 ^ (L + 1) - 2 * (val L f : ℤ)
        + (2 ^ (L + 1) - 2) + ce * e := by
    rw [hc, hd, hr]; exact master_value_c0 L e c0 c1 ce f
  have hVdiff : ∑ i, c' i * (r i : ℤ)
      = (∑ i, c i * (r i : ℤ)) - 2 * (2 ^ (L + 1) - 1) := by
    rw [hc', hc, masterCoeff_mul_sum, masterCoeff_mul_sum]
    have hsplit : ∀ j : Fin L,
        d' j * ((r (tauC L j.val j.isLt) : ℕ) : ℤ)
          = d j * ((r (tauC L j.val j.isLt) : ℕ) : ℤ)
            + (if j.val = a then (-4 : ℤ) else 0)
              * ((r (tauC L j.val j.isLt) : ℕ) : ℤ)
            + (if j.val = a + 1 then (2 : ℤ) else 0)
              * ((r (tauC L j.val j.isLt) : ℕ) : ℤ) := by
      intro j; rw [hd']; ring
    rw [Finset.sum_congr rfl (fun j _ => hsplit j),
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [fin_sum_ite_mul L a haL' (-4)
      (fun j => ((r (tauC L j.val j.isLt) : ℕ) : ℤ))]
    rw [fin_sum_ite_mul L (a + 1) ha1L 2
      (fun j => ((r (tauC L j.val j.isLt) : ℕ) : ℤ))]
    have hτa : ((r (tauC L a haL') : ℕ) : ℤ)
        = 2 ^ (L + 1) - 2 ^ (a + 1) := by
      rw [hr]; exact rliftParentE_tau_int L e a haL'
    have hτa1 : ((r (tauC L (a + 1) ha1L) : ℕ) : ℤ)
        = 2 ^ (L + 1) - 2 ^ (a + 2) := by
      rw [hr]; exact rliftParentE_tau_int L e (a + 1) ha1L
    have hv0 : ((r ⟨0, by omega⟩ : ℕ) : ℤ) = 0 := by
      rw [hr, rliftParentE_zero]; simp
    have hv1 : ((r ⟨1, by omega⟩ : ℕ) : ℤ) = 1 := by
      rw [hr, rliftParentE_one]; simp
    rw [hτa, hτa1, hv0, hv1]
    ring
  obtain ⟨G, hG⟩ := hV
  exact master_pair_contra hβ hg hv c c' hcfloor hc'floor hcsum hc'sum
    (j₀ := extraC L) (by rw [hclast]; exact hce0)
    (by rw [hc'last]; exact hce0) hpar
    ⟨G, by rw [hVc]; exact hG⟩ (Or.inr hVdiff)

/-! ## The coin families -/

/-- Coins for `e ≡ 2 (mod M)`: `x = 2^L − 2^6` plus the four-coin reserve
at exponent 4. -/
def specialTwoF : ℕ → ℕ := fun i =>
  (if i = 4 then 4 else 0) + (if 6 ≤ i then 1 else 0)

lemma specialTwoF_dsum (L : ℕ) (hL : 8 ≤ L) :
    dsum L specialTwoF = L - 2 := by
  unfold dsum
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le 6) (by omega : 6 ≤ L)]
  have h1 : ∑ i ∈ Finset.Ico 0 6, specialTwoF i = 4 := by
    rw [← Finset.range_eq_Ico]
    norm_num [Finset.sum_range_succ, specialTwoF]
  have h2 : ∑ i ∈ Finset.Ico 6 L, specialTwoF i = L - 6 := by
    have hcg : ∀ i ∈ Finset.Ico 6 L, specialTwoF i = 1 := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      unfold specialTwoF
      rw [if_neg (by omega), if_pos (by omega)]
    rw [Finset.sum_congr rfl hcg, Finset.sum_const, Nat.card_Ico,
      smul_eq_mul, mul_one]
  rw [h1, h2]
  omega

lemma specialTwoF_val (L : ℕ) (hL : 8 ≤ L) :
    val L specialTwoF = 2 ^ L := by
  unfold val
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le 6) (by omega : 6 ≤ L)]
  have h1 : ∑ i ∈ Finset.Ico 0 6, specialTwoF i * 2 ^ i = 64 := by
    rw [← Finset.range_eq_Ico]
    norm_num [Finset.sum_range_succ, specialTwoF]
  have h2 : ∑ i ∈ Finset.Ico 6 L, specialTwoF i * 2 ^ i
      = 2 ^ L - 64 := by
    have hcg : ∀ i ∈ Finset.Ico 6 L, specialTwoF i * 2 ^ i = 2 ^ i := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      unfold specialTwoF
      rw [if_neg (by omega), if_pos (by omega)]
      ring
    rw [Finset.sum_congr rfl hcg]
    have hc : (∑ i ∈ Finset.Ico 0 6, 2 ^ i)
        + ∑ i ∈ Finset.Ico 6 L, 2 ^ i
        = ∑ i ∈ Finset.Ico 0 L, 2 ^ i :=
      Finset.sum_Ico_consecutive (fun i => 2 ^ i)
        (Nat.zero_le 6) (by omega : 6 ≤ L)
    have hr1 : ∑ i ∈ Finset.Ico 0 6, 2 ^ i = 63 := by
      rw [← Finset.range_eq_Ico]
      norm_num [Finset.sum_range_succ]
    have hr2 : ∑ i ∈ Finset.Ico 0 L, 2 ^ i = 2 ^ L - 1 := by
      rw [← Finset.range_eq_Ico]
      exact nat_geom_sum L
    have hp : (64 : ℕ) ≤ 2 ^ L := by
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hr1, hr2] at hc
    show (∑ i ∈ Finset.Ico 6 L, 2 ^ i) = 2 ^ L - 64
    omega
  rw [h1, h2]
  have hp : (64 : ℕ) ≤ 2 ^ L := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Coins for `e ≡ 3·2^L (mod 2M)`: `x = 2^{L−1} − 2^6` plus the reserve. -/
def specialThreeF (L : ℕ) : ℕ → ℕ := fun i =>
  (if i = 4 then 4 else 0) + (if 6 ≤ i ∧ i < L - 1 then 1 else 0)

lemma specialThreeF_dsum (L : ℕ) (hL : 8 ≤ L) :
    dsum L (specialThreeF L) = L - 3 := by
  unfold dsum
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le 6) (by omega : 6 ≤ L),
    ← Finset.sum_Ico_consecutive _ (by omega : 6 ≤ L - 1)
      (by omega : L - 1 ≤ L)]
  have h1 : ∑ i ∈ Finset.Ico 0 6, specialThreeF L i = 4 := by
    rw [← Finset.range_eq_Ico]
    norm_num [Finset.sum_range_succ, specialThreeF]
  have h2 : ∑ i ∈ Finset.Ico 6 (L - 1), specialThreeF L i = L - 1 - 6 := by
    have hcg : ∀ i ∈ Finset.Ico 6 (L - 1), specialThreeF L i = 1 := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      unfold specialThreeF
      rw [if_neg (by omega), if_pos (by omega)]
    rw [Finset.sum_congr rfl hcg, Finset.sum_const, Nat.card_Ico,
      smul_eq_mul, mul_one]
  have h3 : ∑ i ∈ Finset.Ico (L - 1) L, specialThreeF L i = 0 := by
    have hcg : ∀ i ∈ Finset.Ico (L - 1) L, specialThreeF L i = 0 := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      unfold specialThreeF
      rw [if_neg (by omega), if_neg (by omega)]
    rw [Finset.sum_congr rfl hcg, Finset.sum_const, smul_zero]
  rw [h1, h2, h3]
  omega

lemma specialThreeF_val (L : ℕ) (hL : 8 ≤ L) :
    val L (specialThreeF L) = 2 ^ (L - 1) := by
  unfold val
  rw [Finset.range_eq_Ico,
    ← Finset.sum_Ico_consecutive _ (Nat.zero_le 6) (by omega : 6 ≤ L),
    ← Finset.sum_Ico_consecutive _ (by omega : 6 ≤ L - 1)
      (by omega : L - 1 ≤ L)]
  have h1 : ∑ i ∈ Finset.Ico 0 6, specialThreeF L i * 2 ^ i = 64 := by
    rw [← Finset.range_eq_Ico]
    norm_num [Finset.sum_range_succ, specialThreeF]
  have h2 : ∑ i ∈ Finset.Ico 6 (L - 1), specialThreeF L i * 2 ^ i
      = 2 ^ (L - 1) - 64 := by
    have hcg : ∀ i ∈ Finset.Ico 6 (L - 1),
        specialThreeF L i * 2 ^ i = 2 ^ i := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      unfold specialThreeF
      rw [if_neg (by omega), if_pos (by omega)]
      ring
    rw [Finset.sum_congr rfl hcg]
    have hc : (∑ i ∈ Finset.Ico 0 6, 2 ^ i)
        + ∑ i ∈ Finset.Ico 6 (L - 1), 2 ^ i
        = ∑ i ∈ Finset.Ico 0 (L - 1), 2 ^ i :=
      Finset.sum_Ico_consecutive (fun i => 2 ^ i)
        (Nat.zero_le 6) (by omega : 6 ≤ L - 1)
    have hr1 : ∑ i ∈ Finset.Ico 0 6, 2 ^ i = 63 := by
      rw [← Finset.range_eq_Ico]
      norm_num [Finset.sum_range_succ]
    have hr2 : ∑ i ∈ Finset.Ico 0 (L - 1), 2 ^ i = 2 ^ (L - 1) - 1 := by
      rw [← Finset.range_eq_Ico]
      exact nat_geom_sum (L - 1)
    have hp : (64 : ℕ) ≤ 2 ^ (L - 1) := by
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hr1, hr2] at hc
    show (∑ i ∈ Finset.Ico 6 (L - 1), 2 ^ i) = 2 ^ (L - 1) - 64
    omega
  have h3 : ∑ i ∈ Finset.Ico (L - 1) L, specialThreeF L i * 2 ^ i = 0 := by
    have hcg : ∀ i ∈ Finset.Ico (L - 1) L,
        specialThreeF L i * 2 ^ i = 0 := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      unfold specialThreeF
      rw [if_neg (by omega), if_neg (by omega)]
      ring
    rw [Finset.sum_congr rfl hcg, Finset.sum_const, smul_zero]
  rw [h1, h2, h3]
  have hp : (64 : ℕ) ≤ 2 ^ (L - 1) := by
    calc (64 : ℕ) = 2 ^ 6 := by norm_num
    _ ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Coins for the sporadic `(m, e) = (9, 10)` case: `x = 3` plus the
reserve at exponent 6. -/
def specialNineF : ℕ → ℕ := fun i =>
  if i = 0 ∨ i = 1 then 1 else if i = 6 then 4 else 0

/-! ## The three special theorems -/

/-- Special certificate for `e ≡ 2 (mod M)` (both sheets). -/
theorem special_modM_two_not_valid (L e : ℕ) (hL : 8 ≤ L)
    (hres : e % (2 ^ (L + 1) - 1) = 2)
    {g β : Fin (L + 3) → ZMod (2 ^ (L + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet L)
    (hg : ∀ i, g i = ((rliftParentE L e i : ℕ) : ZMod (2 ^ (L + 3) - 4))
        + β i) :
    ¬ ValidTuple g := by
  have hds := specialTwoF_dsum L hL
  have hval := specialTwoF_val L hL
  have hdsZ : (dsum L specialTwoF : ℤ) = (L : ℤ) - 2 := by
    rw [hds]; omega
  have hvalZ : (val L specialTwoF : ℤ) = 2 ^ L := by
    rw [hval]; push_cast; ring
  set γ : ℕ := e / (2 ^ (L + 1) - 1) with hγ
  have heZ : (e : ℤ) = 2 + ((2 : ℤ) ^ (L + 1) - 1) * γ := by
    have hda := Nat.div_add_mod e (2 ^ (L + 1) - 1)
    rw [hres, ← hγ] at hda
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hda
    push_cast at hcast
    rw [mersenne_cast] at hcast
    linarith
  refine special_pair_not_valid_core L e specialTwoF 4 (by omega)
    (by norm_num [specialTwoF]) 0 0 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [hdsZ]; ring)
    ⟨(γ : ℤ) - 1, ?_⟩ hβ hg
  rw [hdsZ, hvalZ, heZ]
  ring

/-- Special certificate for `e ≡ 3·2^L (mod 2M)` (one residue). -/
theorem special_threeHalf_not_valid (L e : ℕ) (hL : 8 ≤ L)
    (hres : e % (2 * (2 ^ (L + 1) - 1)) = 3 * 2 ^ L)
    {g β : Fin (L + 3) → ZMod (2 ^ (L + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet L)
    (hg : ∀ i, g i = ((rliftParentE L e i : ℕ) : ZMod (2 ^ (L + 3) - 4))
        + β i) :
    ¬ ValidTuple g := by
  have hds := specialThreeF_dsum L hL
  have hval := specialThreeF_val L hL
  have hdsZ : (dsum L (specialThreeF L) : ℤ) = (L : ℤ) - 3 := by
    rw [hds]; omega
  have hvn : 2 * val L (specialThreeF L) = 2 ^ L := by
    rw [hval]
    have hL1 : L - 1 + 1 = L := by omega
    have hp := pow_succ 2 (L - 1)
    rw [hL1] at hp
    omega
  have hvalZ : (2 : ℤ) * (val L (specialThreeF L) : ℤ) = 2 ^ L := by
    exact_mod_cast hvn
  set γ : ℕ := e / (2 * (2 ^ (L + 1) - 1)) with hγ
  have heZ : (e : ℤ) = 3 * 2 ^ L + 2 * ((2 : ℤ) ^ (L + 1) - 1) * γ := by
    have hda := Nat.div_add_mod e (2 * (2 ^ (L + 1) - 1))
    rw [hres, ← hγ] at hda
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hda
    push_cast at hcast
    rw [mersenne_cast] at hcast
    linarith
  refine special_pair_not_valid_core L e (specialThreeF L) 4 (by omega)
    (by norm_num [specialThreeF]) 0 0 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [hdsZ]; ring)
    ⟨1 + 3 * (γ : ℤ), ?_⟩ hβ hg
  rw [hdsZ, hvalZ, heZ]
  ring

/-- Special certificate for the sporadic `(m, e) = (9, 10)` family. -/
theorem special_sporadic_not_valid (e : ℕ)
    (hres : e % 1022 = 10)
    {g β : Fin (8 + 3) → ZMod (2 ^ (8 + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet 8)
    (hg : ∀ i, g i = ((rliftParentE 8 e i : ℕ) : ZMod (2 ^ (8 + 3) - 4))
        + β i) :
    ¬ ValidTuple g := by
  have hds : dsum 8 specialNineF = 6 := by
    norm_num [dsum, Finset.sum_range_succ, specialNineF]
  have hval : val 8 specialNineF = 259 := by
    norm_num [val, Finset.sum_range_succ, specialNineF]
  set γ : ℕ := e / 1022 with hγ
  have heZ : (e : ℤ) = 10 + 1022 * γ := by
    have hda := Nat.div_add_mod e 1022
    rw [hres, ← hγ] at hda
    have hcast := congrArg (fun n : ℕ => (n : ℤ)) hda
    push_cast at hcast
    linarith
  refine special_pair_not_valid_core 8 e specialNineF 6 (by omega)
    (by norm_num [specialNineF]) 1 0 1 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by rw [hds]; norm_num)
    ⟨(γ : ℤ) - 1, ?_⟩ hβ hg
  rw [hds, hval, heZ]
  push_cast
  ring

end MinModulus

