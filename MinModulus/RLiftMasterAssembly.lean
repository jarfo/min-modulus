import MinModulus.RLiftMasterPair
import MinModulus.RLiftMasterCover
import MinModulus.RLiftGridTable

/-!
# Master family: assembling the rival pair from representation certificates

From a `RepCert` for the derived target `u` (or its reflection `w`), we build
the base master rival `c` (coefficients `c1` at the unit, `f j − 1` at `τ_j`,
`ce` at the extra) and its shift partner `c' = c + z₁` (using the doubled coin
at exponent `b`), prove both are admissible with equal odd-support parity and
integer values differing by exactly `±2M`, with the base value a multiple of
`2M`, and conclude via `master_pair_contra` that the parent tuple is invalid.
-/

set_option maxHeartbeats 1600000

namespace MinModulus

open Finset

/-! ## The master coefficient vector -/

/-- Master coefficient vector: `c0` at the zero coin, `c1` at the unit,
`d j` at `τ_j`, `ce` at the extra. -/
def masterCoeff (L : ℕ) (c0 c1 : ℤ) (d : Fin L → ℤ) (ce : ℤ) :
    Fin (L + 3) → ℤ :=
  Fin.cons c0 (Fin.cons c1 (Fin.snoc d ce))

lemma masterCoeff_last (L : ℕ) (c0 c1 ce : ℤ) (d : Fin L → ℤ) :
    masterCoeff L c0 c1 d ce (extraC L) = ce := by
  have h1 : extraC L = Fin.succ (Fin.succ (Fin.last L)) := by
    apply Fin.ext; simp [extraC, Fin.succ]
  rw [h1, masterCoeff, Fin.cons_succ, Fin.cons_succ, Fin.snoc_last]

/-- Generic weighted-sum splitter over the cons/cons/snoc structure. -/
lemma masterCoeff_mul_sum (L : ℕ) (c0 c1 ce : ℤ) (d : Fin L → ℤ)
    (v : Fin (L + 3) → ℤ) :
    ∑ i, masterCoeff L c0 c1 d ce i * v i
      = c0 * v ⟨0, by omega⟩ + c1 * v ⟨1, by omega⟩
        + (∑ j : Fin L, d j * v (tauC L j.val j.isLt))
        + ce * v (extraC L) := by
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_succ]
  rw [Fin.sum_univ_castSucc]
  simp only [masterCoeff, Fin.cons_zero, Fin.cons_succ, Fin.snoc_castSucc,
    Fin.snoc_last]
  have h0 : (0 : Fin (L + 3)) = ⟨0, by omega⟩ := by apply Fin.ext; simp
  have h1 : Fin.succ (0 : Fin (L + 2)) = (⟨1, by omega⟩ : Fin (L + 3)) := by
    apply Fin.ext; simp
  have hτ : ∀ j : Fin L,
      Fin.succ (Fin.succ (Fin.castSucc j)) = tauC L j.val j.isLt := by
    intro j; apply Fin.ext; simp [tauC, Fin.succ]
  have he : Fin.succ (Fin.succ (Fin.last L)) = extraC L := by
    apply Fin.ext; simp [extraC, Fin.succ]
  rw [h0, h1, he]
  rw [Finset.sum_congr rfl (fun j _ => by rw [hτ j])]
  ring

lemma sum_masterCoeff (L : ℕ) (c0 c1 ce : ℤ) (d : Fin L → ℤ) :
    ∑ i, masterCoeff L c0 c1 d ce i = c0 + c1 + (∑ j : Fin L, d j) + ce := by
  have h := masterCoeff_mul_sum L c0 c1 ce d (fun _ => 1)
  simpa using h

/-- Pointwise floor over the cons/cons/snoc structure. -/
lemma masterCoeff_floor (L : ℕ) (c0 c1 ce : ℤ) (d : Fin L → ℤ)
    (h0 : -1 ≤ c0) (h1 : -1 ≤ c1) (hd : ∀ j, -1 ≤ d j) (he : -1 ≤ ce) :
    ∀ i, -1 ≤ masterCoeff L c0 c1 d ce i := by
  intro i
  refine Fin.cases ?_ (fun i1 => ?_) i
  · simpa [masterCoeff] using h0
  · rw [masterCoeff, Fin.cons_succ]
    refine Fin.cases ?_ (fun i2 => ?_) i1
    · simpa using h1
    · rw [Fin.cons_succ]
      refine Fin.lastCases ?_ (fun j => ?_) i2
      · rw [Fin.snoc_last]; exact he
      · rw [Fin.snoc_castSucc]; exact hd j

/-- Pointwise even-difference over the cons/cons/snoc structure. -/
lemma masterCoeff_even_diff (L : ℕ) (c0 c0' c1 c1' ce ce' : ℤ)
    (d d' : Fin L → ℤ)
    (h0 : ∃ t, c0' = c0 + 2 * t) (h1 : ∃ t, c1' = c1 + 2 * t)
    (hd : ∀ j, ∃ t, d' j = d j + 2 * t) (he : ∃ t, ce' = ce + 2 * t) :
    ∀ i, ∃ t, masterCoeff L c0' c1' d' ce' i
        = masterCoeff L c0 c1 d ce i + 2 * t := by
  intro i
  refine Fin.cases ?_ (fun i1 => ?_) i
  · simpa [masterCoeff] using h0
  · rw [masterCoeff, masterCoeff, Fin.cons_succ, Fin.cons_succ]
    refine Fin.cases ?_ (fun i2 => ?_) i1
    · simpa using h1
    · rw [Fin.cons_succ, Fin.cons_succ]
      refine Fin.lastCases ?_ (fun j => ?_) i2
      · rw [Fin.snoc_last, Fin.snoc_last]; exact he
      · rw [Fin.snoc_castSucc, Fin.snoc_castSucc]; exact hd j

lemma odd_iff_of_even_diff {a b : ℤ} (h : ∃ t, b = a + 2 * t) :
    Odd a ↔ Odd b := by
  obtain ⟨t, rfl⟩ := h
  constructor
  · rintro ⟨s, rfl⟩; exact ⟨s + t, by ring⟩
  · rintro ⟨s, hs⟩; exact ⟨s - t, by omega⟩

/-! ## Sum helpers -/

lemma fin_sum_ite_mul (L b : ℕ) (hb : b < L) (c : ℤ) (w : Fin L → ℤ) :
    ∑ j : Fin L, (if j.val = b then c else 0) * w j = c * w ⟨b, hb⟩ := by
  rw [Finset.sum_eq_single (⟨b, hb⟩ : Fin L)]
  · simp
  · intro j _ hj
    have hne : j.val ≠ b := fun h => hj (Fin.ext h)
    simp [hne]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The `τ` values of the parent, as integers. -/
lemma rliftParentE_tau_int (L e : ℕ) (j : ℕ) (h : j < L) :
    ((rliftParentE L e (tauC L j h) : ℕ) : ℤ)
      = 2 ^ (L + 1) - 2 ^ (j + 1) := by
  rw [rliftParentE_tau L e j h]
  have h1 : (2 : ℕ) ^ (j + 1) ≤ 2 ^ (L + 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : (1 : ℕ) ≤ 2 ^ (j + 1) := Nat.one_le_pow _ _ (by norm_num)
  have h3 : (2 : ℕ) ^ (L + 1) - 1 - (2 ^ (j + 1) - 1)
      = 2 ^ (L + 1) - 2 ^ (j + 1) := by omega
  rw [h3, Nat.cast_sub h1]
  push_cast
  ring

/-- Geometric sum `∑_{i<n} 2^i = 2^n − 1` over `ℤ`. -/
lemma int_geom_sum (n : ℕ) : ∑ i ∈ range n, (2 : ℤ) ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

/-! ## The closed value formula -/

/-- Integer value of the base master rival against the parent values. -/
lemma master_value (L e : ℕ) (c1 ce : ℤ) (f : ℕ → ℕ) :
    ∑ i, masterCoeff L 0 c1 (fun j => (f j.val : ℤ) - 1) ce i
        * ((rliftParentE L e i : ℕ) : ℤ)
      = c1 + ((dsum L f : ℤ) - L) * 2 ^ (L + 1) - 2 * (val L f : ℤ)
        + (2 ^ (L + 1) - 2) + ce * e := by
  rw [masterCoeff_mul_sum]
  rw [show ((rliftParentE L e ⟨0, by omega⟩ : ℕ) : ℤ) = 0 by
    rw [rliftParentE_zero]; simp]
  rw [show ((rliftParentE L e ⟨1, by omega⟩ : ℕ) : ℤ) = 1 by
    rw [rliftParentE_one]; simp]
  rw [show ((rliftParentE L e (extraC L) : ℕ) : ℤ) = e by
    rw [rliftParentE_last]]
  have hτ : ∑ j : Fin L, ((f j.val : ℤ) - 1)
        * ((rliftParentE L e (tauC L j.val j.isLt) : ℕ) : ℤ)
      = ((dsum L f : ℤ) - L) * 2 ^ (L + 1) - 2 * (val L f : ℤ)
        + (2 ^ (L + 1) - 2) := by
    rw [Finset.sum_congr rfl
      (fun j _ => by rw [rliftParentE_tau_int L e j.val j.isLt])]
    have hsplit : ∀ j : Fin L,
        ((f j.val : ℤ) - 1) * (2 ^ (L + 1) - 2 ^ (j.val + 1))
          = (f j.val : ℤ) * 2 ^ (L + 1) - 2 ^ (L + 1)
            - ((f j.val : ℤ) * 2 ^ j.val) * 2 + 2 ^ j.val * 2 := by
      intro j
      rw [pow_succ]
      ring
    rw [Finset.sum_congr rfl (fun j _ => hsplit j)]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
    have hf : ∑ j : Fin L, (f j.val : ℤ) = (dsum L f : ℤ) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (f i : ℤ)) L]
      rw [dsum]
      push_cast
      rfl
    have hfv : ∑ j : Fin L, (f j.val : ℤ) * 2 ^ j.val = (val L f : ℤ) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (f i : ℤ) * 2 ^ i) L]
      rw [val]
      push_cast
      rfl
    have hconst : ∑ _j : Fin L, (2 : ℤ) ^ (L + 1) = L * 2 ^ (L + 1) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hpow : ∑ j : Fin L, (2 : ℤ) ^ j.val = 2 ^ L - 1 := by
      rw [Fin.sum_univ_eq_sum_range (fun i => (2 : ℤ) ^ i) L]
      exact int_geom_sum L
    rw [hf, hfv, hconst, hpow, pow_succ]
    ring
  rw [hτ]
  ring

/-! ## The doubled-coin count -/

/-- Coin counts with a doubled coin at exponent `b`. -/
def masterF (k : ℕ → ℕ) (b : ℕ) : ℕ → ℕ :=
  fun i => k i + if i = b then 2 else 0

lemma masterF_self (k : ℕ → ℕ) (b : ℕ) : 2 ≤ masterF k b b := by
  simp [masterF]

lemma masterF_val (L b : ℕ) (k : ℕ → ℕ) (hb : b < L) :
    val L (masterF k b) = val L k + 2 ^ (b + 1) := by
  unfold val masterF
  rw [Finset.sum_congr rfl (fun i _ => by
    show (k i + if i = b then 2 else 0) * 2 ^ i
      = k i * 2 ^ i + (if i = b then 2 * 2 ^ i else 0)
    split <;> ring)]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (range L) b
    (fun i => 2 * 2 ^ i)]
  rw [if_pos (Finset.mem_range.mpr hb), pow_succ]
  ring

lemma masterF_dsum (L b : ℕ) (k : ℕ → ℕ) (hb : b < L) :
    dsum L (masterF k b) = dsum L k + 2 := by
  unfold dsum masterF
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' (range L) b (fun _ => 2)]
  rw [if_pos (Finset.mem_range.mpr hb)]

/-! ## The core pair contradiction -/

/-- Core theorem: a nonnegative coin family `f` with a two-coin reserve at
exponent `b`, coefficient sum matching `c1, ce`, and value a multiple of `2M`
yields the master rival pair, contradicting validity of the parent. -/
theorem master_pair_not_valid_core (L e : ℕ) (f : ℕ → ℕ) (b : ℕ)
    (hbL : b < L) (hfb : 2 ≤ f b) (c1 ce : ℤ)
    (hc1 : c1 = 1 ∨ c1 = 2) (hce : ce = 1 ∨ ce = -1)
    (hF : (dsum L f : ℤ) = L - c1 - ce)
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
  -- base rival
  set c : Fin (L + 3) → ℤ := masterCoeff L 0 c1 d ce with hc
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
    rw [hc, sum_masterCoeff, hdsum, hF]
    ring
  have hcfloor : ∀ i, -1 ≤ c i := by
    rw [hc]
    refine masterCoeff_floor L 0 c1 ce d (by norm_num) (by omega) ?_
      (by omega)
    intro j
    have := Int.natCast_nonneg (f j.val)
    simp only [hd]
    omega
  have hclast : c (extraC L) = ce := by rw [hc, masterCoeff_last]
  have hcene : ce ≠ 0 := by omega
  -- the partner, split on b = 0
  rcases Nat.eq_zero_or_pos b with hb0 | hb1
  · -- zero-coin variant: subtract 2 at τ_0, add 4 at the zero coin
    subst hb0
    set d' : Fin L → ℤ := fun j => d j + if j.val = 0 then -2 else 0 with hd'
    set c' : Fin (L + 3) → ℤ := masterCoeff L 4 (c1 - 2) d' ce with hc'
    have hd'sum : ∑ j : Fin L, d' j = (∑ j : Fin L, d j) + -2 := by
      rw [hd', Finset.sum_add_distrib]
      congr 1
      have := fin_sum_ite_mul L 0 hbL (-2) (fun _ => 1)
      simpa using this
    have hc'sum : ∑ i, c' i = 0 := by
      rw [hc', sum_masterCoeff, hd'sum, hdsum, hF]
      ring
    have hc'floor : ∀ i, -1 ≤ c' i := by
      rw [hc']
      refine masterCoeff_floor L 4 (c1 - 2) ce d' (by norm_num) (by omega)
        ?_ (by omega)
      intro j
      have h0 := Int.natCast_nonneg (f j.val)
      simp only [hd', hd]
      by_cases hj : j.val = 0
      · have hfj : (2 : ℤ) ≤ (f j.val : ℤ) := by
          have hfe : f j.val = f 0 := by rw [hj]
          rw [hfe]; exact_mod_cast hfb
        simp only [if_pos hj]
        omega
      · simp only [if_neg hj]
        omega
    have hc'last : c' (extraC L) = ce := by rw [hc', masterCoeff_last]
    have hpar : ∀ i, Odd (c i) ↔ Odd (c' i) := by
      intro i
      refine odd_iff_of_even_diff ?_
      rw [hc, hc']
      refine masterCoeff_even_diff L 0 4 c1 (c1 - 2) ce ce d d'
        ⟨2, by ring⟩ ⟨-1, by ring⟩ ?_ ⟨0, by ring⟩ i
      intro j
      by_cases hj : j.val = 0
      · exact ⟨-1, by simp only [hd', if_pos hj]; ring⟩
      · exact ⟨0, by simp only [hd', if_neg hj]; ring⟩
    -- values
    have hVc : ∑ i, c i * (r i : ℤ)
        = c1 + ((dsum L f : ℤ) - L) * 2 ^ (L + 1) - 2 * (val L f : ℤ)
          + (2 ^ (L + 1) - 2) + ce * e := by
      rw [hc, hd, hr]; exact master_value L e c1 ce f
    have hVdiff : ∑ i, c' i * (r i : ℤ)
        = (∑ i, c i * (r i : ℤ)) - 2 * (2 ^ (L + 1) - 1) := by
      rw [hc', hc, masterCoeff_mul_sum, masterCoeff_mul_sum]
      have hsplit : ∀ j : Fin L,
          d' j * ((r (tauC L j.val j.isLt) : ℕ) : ℤ)
            = d j * ((r (tauC L j.val j.isLt) : ℕ) : ℤ)
              + (if j.val = 0 then (-2 : ℤ) else 0)
                * ((r (tauC L j.val j.isLt) : ℕ) : ℤ) := by
        intro j; rw [hd']; ring
      rw [Finset.sum_congr rfl (fun j _ => hsplit j),
        Finset.sum_add_distrib]
      rw [fin_sum_ite_mul L 0 hbL (-2)
        (fun j => ((r (tauC L j.val j.isLt) : ℕ) : ℤ))]
      have hτ0 : ((r (tauC L 0 hbL) : ℕ) : ℤ) = 2 ^ (L + 1) - 2 ^ 1 := by
        rw [hr]; exact rliftParentE_tau_int L e 0 hbL
      have hv0 : ((r ⟨0, by omega⟩ : ℕ) : ℤ) = 0 := by
        rw [hr, rliftParentE_zero]; simp
      have hv1 : ((r ⟨1, by omega⟩ : ℕ) : ℤ) = 1 := by
        rw [hr, rliftParentE_one]; simp
      rw [hτ0, hv0, hv1]
      ring
    obtain ⟨G, hG⟩ := hV
    refine master_pair_contra hβ hg hv c c' hcfloor hc'floor hcsum hc'sum
      (j₀ := extraC L) (by rw [hclast]; exact hcene)
      (by rw [hc'last]; exact hcene) hpar
      ⟨G, by rw [hVc]; exact hG⟩ (Or.inr hVdiff)
  · -- interior variant: subtract 2 at τ_b, add 4 at τ_{b−1}
    set bp : ℕ := b - 1 with hbp
    have hbpL : bp < L := by omega
    have hbpb : bp + 1 = b := by omega
    have hbne : b ≠ bp := by omega
    set d' : Fin L → ℤ := fun j =>
      d j + (if j.val = b then -2 else 0) + (if j.val = bp then 4 else 0)
      with hd'
    set c' : Fin (L + 3) → ℤ := masterCoeff L 0 (c1 - 2) d' ce with hc'
    have hd'sum : ∑ j : Fin L, d' j = (∑ j : Fin L, d j) + 2 := by
      rw [hd']
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      have h1 := fin_sum_ite_mul L b hbL (-2) (fun _ => 1)
      have h2 := fin_sum_ite_mul L bp hbpL 4 (fun _ => 1)
      simp only [mul_one] at h1 h2
      rw [h1, h2]
      ring
    have hc'sum : ∑ i, c' i = 0 := by
      rw [hc', sum_masterCoeff, hd'sum, hdsum, hF]
      ring
    have hc'floor : ∀ i, -1 ≤ c' i := by
      rw [hc']
      refine masterCoeff_floor L 0 (c1 - 2) ce d' (by norm_num) (by omega)
        ?_ (by omega)
      intro j
      have h0 := Int.natCast_nonneg (f j.val)
      simp only [hd', hd]
      by_cases hjb : j.val = b
      · have hfj : (2 : ℤ) ≤ (f j.val : ℤ) := by
          have hfe : f j.val = f b := by rw [hjb]
          rw [hfe]; exact_mod_cast hfb
        have hjbp : ¬ j.val = bp := by omega
        simp only [if_pos hjb, if_neg hjbp]
        omega
      · by_cases hjp : j.val = bp
        · simp only [if_neg hjb, if_pos hjp]
          omega
        · simp only [if_neg hjb, if_neg hjp]
          omega
    have hc'last : c' (extraC L) = ce := by rw [hc', masterCoeff_last]
    have hpar : ∀ i, Odd (c i) ↔ Odd (c' i) := by
      intro i
      refine odd_iff_of_even_diff ?_
      rw [hc, hc']
      refine masterCoeff_even_diff L 0 0 c1 (c1 - 2) ce ce d d'
        ⟨0, by ring⟩ ⟨-1, by ring⟩ ?_ ⟨0, by ring⟩ i
      intro j
      by_cases hjb : j.val = b
      · have hjbp : ¬ j.val = bp := by omega
        exact ⟨-1, by simp only [hd', if_pos hjb, if_neg hjbp]; ring⟩
      · by_cases hjp : j.val = bp
        · exact ⟨2, by simp only [hd', if_neg hjb, if_pos hjp]; ring⟩
        · exact ⟨0, by simp only [hd', if_neg hjb, if_neg hjp]; ring⟩
    have hVc : ∑ i, c i * (r i : ℤ)
        = c1 + ((dsum L f : ℤ) - L) * 2 ^ (L + 1) - 2 * (val L f : ℤ)
          + (2 ^ (L + 1) - 2) + ce * e := by
      rw [hc, hd, hr]; exact master_value L e c1 ce f
    have hVdiff : ∑ i, c' i * (r i : ℤ)
        = (∑ i, c i * (r i : ℤ)) + 2 * (2 ^ (L + 1) - 1) := by
      rw [hc', hc, masterCoeff_mul_sum, masterCoeff_mul_sum]
      have hsplit : ∀ j : Fin L,
          d' j * ((r (tauC L j.val j.isLt) : ℕ) : ℤ)
            = d j * ((r (tauC L j.val j.isLt) : ℕ) : ℤ)
              + (if j.val = b then (-2 : ℤ) else 0)
                * ((r (tauC L j.val j.isLt) : ℕ) : ℤ)
              + (if j.val = bp then (4 : ℤ) else 0)
                * ((r (tauC L j.val j.isLt) : ℕ) : ℤ) := by
        intro j; rw [hd']; ring
      rw [Finset.sum_congr rfl (fun j _ => hsplit j),
        Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [fin_sum_ite_mul L b hbL (-2)
        (fun j => ((r (tauC L j.val j.isLt) : ℕ) : ℤ))]
      rw [fin_sum_ite_mul L bp hbpL 4
        (fun j => ((r (tauC L j.val j.isLt) : ℕ) : ℤ))]
      have hτb : ((r (tauC L b hbL) : ℕ) : ℤ)
          = 2 ^ (L + 1) - 2 ^ (b + 1) := by
        rw [hr]; exact rliftParentE_tau_int L e b hbL
      have hτp : ((r (tauC L bp hbpL) : ℕ) : ℤ)
          = 2 ^ (L + 1) - 2 ^ b := by
        rw [hr, rliftParentE_tau_int L e bp hbpL, hbpb]
      have hv0 : ((r ⟨0, by omega⟩ : ℕ) : ℤ) = 0 := by
        rw [hr, rliftParentE_zero]; simp
      have hv1 : ((r ⟨1, by omega⟩ : ℕ) : ℤ) = 1 := by
        rw [hr, rliftParentE_one]; simp
      rw [hτb, hτp, hv0, hv1]
      ring
    obtain ⟨G, hG⟩ := hV
    refine master_pair_contra hβ hg hv c c' hcfloor hc'floor hcsum hc'sum
      (j₀ := extraC L) (by rw [hclast]; exact hcene)
      (by rw [hc'last]; exact hcene) hpar
      ⟨G, by rw [hVc]; exact hG⟩ (Or.inl hVdiff)

/-! ## Parity and target wrappers -/

/-- `M = 2^(L+1) − 1` is odd. -/
lemma mersenne_odd (L : ℕ) : Odd (2 ^ (L + 1) - 1 : ℕ) := by
  have hp : (2 : ℕ) ^ (L + 1) = 2 * 2 ^ L := by rw [pow_succ]; ring
  have h1 : (1 : ℕ) ≤ 2 ^ L := Nat.one_le_pow _ _ (by norm_num)
  exact ⟨2 ^ L - 1, by omega⟩

lemma mersenne_cast (L : ℕ) :
    ((2 ^ (L + 1) - 1 : ℕ) : ℤ) = 2 ^ (L + 1) - 1 := by
  have h1 : (1 : ℕ) ≤ 2 ^ (L + 1) := Nat.one_le_pow _ _ (by norm_num)
  rw [Nat.cast_sub h1]
  push_cast
  ring

/-- A `RepCert` at the direct target `u` kills the parent (`ce = −1`). -/
theorem master_u_not_valid (L e u B : ℕ) (hL : 8 ≤ L)
    (hgM : (2 * u + e) % (2 ^ (L + 1) - 1) = 0)
    (hB : (Odd e ∧ B = L - 2) ∨ (Even e ∧ B = L - 3))
    (hcert : RepCert (L + 1) B u)
    {g β : Fin (L + 3) → ZMod (2 ^ (L + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet L)
    (hg : ∀ i, g i = ((rliftParentE L e i : ℕ) : ZMod (2 ^ (L + 3) - 4))
        + β i) :
    ¬ ValidTuple g := by
  obtain ⟨b, x, k, hb2, hmod, hBx, hval, hds⟩ := hcert
  simp only [Nat.add_sub_cancel] at hval hds
  have hbL : b < L := by omega
  set f := masterF k b with hf
  have hfb : 2 ≤ f b := masterF_self k b
  have hfval : val L f = x + 2 ^ (b + 1) := by
    rw [hf, masterF_val L b k hbL, hval]
  have hfds : dsum L f = B + 2 := by
    rw [hf, masterF_dsum L b k hbL, hds]
  -- δ from the residue certificate
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd (n := 2 ^ (L + 1) - 1)).mp hmod
  rw [mersenne_cast] at ht
  push_cast at ht
  have hδ : (x : ℤ) + 2 ^ (b + 1)
      = (u : ℤ) - (2 ^ (L + 1) - 1) * t := by linarith
  -- g from the target relation
  obtain ⟨g, hgnat⟩ := Nat.dvd_of_mod_eq_zero hgM
  have hgZ : 2 * (u : ℤ) + (e : ℤ) = (2 ^ (L + 1) - 1) * (g : ℤ) := by
    have hc : 2 * (u : ℤ) + (e : ℤ)
        = ((2 ^ (L + 1) - 1 : ℕ) : ℤ) * (g : ℤ) := by exact_mod_cast hgnat
    rw [mersenne_cast] at hc
    exact hc
  have hvalZ : (val L f : ℤ) = (x : ℤ) + 2 ^ (b + 1) := by
    rw [hfval]; push_cast; ring
  rcases hB with ⟨he, hBeq⟩ | ⟨he, hBeq⟩
  · -- odd e: c1 = 1
    obtain ⟨g', hg'⟩ : Odd g := by
      have ho2 : Odd (2 * u + e) := by
        obtain ⟨s, hs⟩ := he; exact ⟨u + s, by omega⟩
      rw [hgnat] at ho2
      exact (Nat.odd_mul.mp ho2).2
    have hgZ' : (g : ℤ) = 2 * (g' : ℤ) + 1 := by omega
    have hdsL : (dsum L f : ℤ) = (L : ℤ) := by
      have : dsum L f = L := by omega
      rw [this]
    refine master_pair_not_valid_core L e f b hbL hfb 1 (-1) (Or.inl rfl)
      (Or.inr rfl) (by rw [hdsL]; ring) ⟨(t : ℤ) - g', ?_⟩ hβ hg
    rw [hdsL, hvalZ]
    linear_combination (-2 : ℤ) * hδ - hgZ - (2 ^ (L + 1) - 1) * hgZ'
  · -- even e: c1 = 2
    obtain ⟨g', hg'⟩ : Even g := by
      have he2 : Even (2 * u + e) := by
        obtain ⟨s, hs⟩ := he; exact ⟨u + s, by omega⟩
      rw [hgnat] at he2
      rcases Nat.even_mul.mp he2 with h | h
      · obtain ⟨s, hs⟩ := mersenne_odd L
        obtain ⟨r, hr⟩ := h
        omega
      · exact h
    have hgZ' : (g : ℤ) = 2 * (g' : ℤ) := by omega
    have hdsL : (dsum L f : ℤ) = (L : ℤ) - 1 := by
      have : dsum L f = L - 1 := by omega
      rw [this]; omega
    refine master_pair_not_valid_core L e f b hbL hfb 2 (-1) (Or.inr rfl)
      (Or.inr rfl) (by rw [hdsL]; ring) ⟨(t : ℤ) - g', ?_⟩ hβ hg
    rw [hdsL, hvalZ]
    linear_combination (-2 : ℤ) * hδ - hgZ - (2 ^ (L + 1) - 1) * hgZ'

/-- A `RepCert` at the reflected target `M − 1 − u` kills the parent
(`ce = +1`). -/
theorem master_w_not_valid (L e u B : ℕ) (hL : 8 ≤ L)
    (hu : u < 2 ^ (L + 1) - 1)
    (hgM : (2 * u + e) % (2 ^ (L + 1) - 1) = 0)
    (hB : (Odd e ∧ B = L - 2) ∨ (Even e ∧ B = L - 3))
    (hcert : RepCert (L + 1) (B - 2) (2 ^ (L + 1) - 2 - u))
    {g β : Fin (L + 3) → ZMod (2 ^ (L + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet L)
    (hg : ∀ i, g i = ((rliftParentE L e i : ℕ) : ZMod (2 ^ (L + 3) - 4))
        + β i) :
    ¬ ValidTuple g := by
  obtain ⟨b, x, k, hb2, hmod, hBx, hval, hds⟩ := hcert
  simp only [Nat.add_sub_cancel] at hval hds
  have hbL : b < L := by omega
  set f := masterF k b with hf
  have hfb : 2 ≤ f b := masterF_self k b
  have hfval : val L f = x + 2 ^ (b + 1) := by
    rw [hf, masterF_val L b k hbL, hval]
  have hBrange : 2 ≤ B := by rcases hB with ⟨_, h⟩ | ⟨_, h⟩ <;> omega
  have hfds : dsum L f = B := by
    rw [hf, masterF_dsum L b k hbL, hds]; omega
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd (n := 2 ^ (L + 1) - 1)).mp hmod
  rw [mersenne_cast] at ht
  have hwZ : ((2 ^ (L + 1) - 2 - u : ℕ) : ℤ)
      = 2 ^ (L + 1) - 2 - (u : ℤ) := by
    have h1 : (1 : ℕ) ≤ 2 ^ (L + 1) := Nat.one_le_pow _ _ (by norm_num)
    have h2 : 2 + u ≤ 2 ^ (L + 1) := by omega
    have h3 : (2 ^ (L + 1) - 2 - u : ℕ) = 2 ^ (L + 1) - (2 + u) := by omega
    rw [h3, Nat.cast_sub h2]
    push_cast
    ring
  rw [hwZ] at ht
  push_cast at ht
  have hδ : (x : ℤ) + 2 ^ (b + 1)
      = (2 ^ (L + 1) - 2 - (u : ℤ)) - (2 ^ (L + 1) - 1) * t := by linarith
  obtain ⟨g, hgnat⟩ := Nat.dvd_of_mod_eq_zero hgM
  have hgZ : 2 * (u : ℤ) + (e : ℤ) = (2 ^ (L + 1) - 1) * (g : ℤ) := by
    have hc : 2 * (u : ℤ) + (e : ℤ)
        = ((2 ^ (L + 1) - 1 : ℕ) : ℤ) * (g : ℤ) := by exact_mod_cast hgnat
    rw [mersenne_cast] at hc
    exact hc
  have hvalZ : (val L f : ℤ) = (x : ℤ) + 2 ^ (b + 1) := by
    rw [hfval]; push_cast; ring
  rcases hB with ⟨he, hBeq⟩ | ⟨he, hBeq⟩
  · -- odd e: c1 = 1
    obtain ⟨g', hg'⟩ : Odd g := by
      have ho2 : Odd (2 * u + e) := by
        obtain ⟨s, hs⟩ := he; exact ⟨u + s, by omega⟩
      rw [hgnat] at ho2
      exact (Nat.odd_mul.mp ho2).2
    have hgZ' : (g : ℤ) = 2 * (g' : ℤ) + 1 := by omega
    have hdsL : (dsum L f : ℤ) = (L : ℤ) - 2 := by
      have : dsum L f = L - 2 := by omega
      rw [this]; omega
    refine master_pair_not_valid_core L e f b hbL hfb 1 1 (Or.inl rfl)
      (Or.inl rfl) (by rw [hdsL]; ring) ⟨(t : ℤ) + g' - 1, ?_⟩ hβ hg
    rw [hdsL, hvalZ]
    linear_combination (-2 : ℤ) * hδ + hgZ + (2 ^ (L + 1) - 1) * hgZ'
  · -- even e: c1 = 2
    obtain ⟨g', hg'⟩ : Even g := by
      have he2 : Even (2 * u + e) := by
        obtain ⟨s, hs⟩ := he; exact ⟨u + s, by omega⟩
      rw [hgnat] at he2
      rcases Nat.even_mul.mp he2 with h | h
      · obtain ⟨s, hs⟩ := mersenne_odd L
        obtain ⟨r, hr⟩ := h
        omega
      · exact h
    have hgZ' : (g : ℤ) = 2 * (g' : ℤ) := by omega
    have hdsL : (dsum L f : ℤ) = (L : ℤ) - 3 := by
      have : dsum L f = L - 3 := by omega
      rw [this]; omega
    refine master_pair_not_valid_core L e f b hbL hfb 2 1 (Or.inr rfl)
      (Or.inl rfl) (by rw [hdsL]; ring) ⟨(t : ℤ) + g' - 2, ?_⟩ hβ hg
    rw [hdsL, hvalZ]
    linear_combination (-2 : ℤ) * hδ + hgZ + (2 ^ (L + 1) - 1) * hgZ'

/-! ## The combined master theorem -/

/-- The master family: for every extra `e` whose derived target `u` is not
in the finite exceptional list, the parent tuple is invalid. -/
theorem master_not_valid (L e u : ℕ) (hL : 8 ≤ L)
    (hu : u < 2 ^ (L + 1) - 1)
    (hgM : (2 * u + e) % (2 ^ (L + 1) - 1) = 0)
    (hex : ¬ (u = 0 ∨ u = 2 ^ (L + 1) - 2 ∨ u = 2 ^ L - 1
        ∨ u = 2 ^ L + 2 ^ (L - 1) - 1 ∨ u = 7 * 2 ^ (L - 2) - 1
        ∨ (Even e ∧
            (u = 2 ^ (L - 1) - 1 ∨ u = 3 * 2 ^ (L - 2) - 1
             ∨ u = 5 * 2 ^ (L - 2) - 1
             ∨ u = 7 * 2 ^ (L - 3) - 1 ∨ u = 11 * 2 ^ (L - 3) - 1
             ∨ u = 13 * 2 ^ (L - 3) - 1 ∨ u = 15 * 2 ^ (L - 3) - 1
             ∨ u = 15 * 2 ^ (L - 4) - 1 ∨ u = 23 * 2 ^ (L - 4) - 1
             ∨ u = 27 * 2 ^ (L - 4) - 1 ∨ u = 29 * 2 ^ (L - 4) - 1
             ∨ (L = 8 ∧ u = 506)))))
    {g β : Fin (L + 3) → ZMod (2 ^ (L + 3) - 4)}
    (hβ : ∀ i, β i = 0 ∨ β i = sheet L)
    (hg : ∀ i, g i = ((rliftParentE L e i : ℕ) : ZMod (2 ^ (L + 3) - 4))
        + β i) :
    ¬ ValidTuple g := by
  rcases Nat.even_or_odd e with he | he
  · -- even e : B = L − 3 = (L+1) − 4
    rcases master_coverage (m := L + 1) (B := L - 3) (by omega)
        (Or.inr (by omega)) hu with
      h | h | h | h | h | h | h | h
    · exact master_u_not_valid L e u (L - 3) hL hgM (Or.inr ⟨he, rfl⟩) h hβ hg
    · exact master_w_not_valid L e u (L - 3) hL hu hgM (Or.inr ⟨he, rfl⟩) h hβ hg
    · exact absurd (Or.inl h) hex
    · exact absurd (Or.inr (Or.inl h)) hex
    · exact absurd (Or.inr (Or.inr (Or.inl h))) hex
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl h)))) hex
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hex
    · refine absurd
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨he, ?_⟩))))) hex
      rcases h.2 with h | h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl h))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl h)))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inl h))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inl h)))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inl h))))))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, h.2⟩))))))))))
  · -- odd e : B = L − 2 = (L+1) − 3
    rcases master_coverage (m := L + 1) (B := L - 2) (by omega)
        (Or.inl (by omega)) hu with
      h | h | h | h | h | h | h | h
    · exact master_u_not_valid L e u (L - 2) hL hgM (Or.inl ⟨he, rfl⟩) h hβ hg
    · exact master_w_not_valid L e u (L - 2) hL hu hgM (Or.inl ⟨he, rfl⟩) h hβ hg
    · exact absurd (Or.inl h) hex
    · exact absurd (Or.inr (Or.inl h)) hex
    · exact absurd (Or.inr (Or.inr (Or.inl h))) hex
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl h)))) hex
    · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hex
    · exact absurd h.1 (by omega)

end MinModulus

