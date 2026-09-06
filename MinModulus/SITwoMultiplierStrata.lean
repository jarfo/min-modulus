/-
# Exact strata for two-extra coherent SI prefixes under any multiplier

For every n>=5, a valid tuple with coherent prefix c*(2^i-1)+b, i<n-2,
satisfies the actual stratumBound, even when c is a nonunit. Below 2^n
its modulus is a power gap. Direct G1 critical exclusion and the full
odd G2 threshold complement the preceding arbitrary-multiplier G3 result.

For retained length m>=5, a new bound 2^(m+2)<=5*B(m) justifies subgroup
index d<=4 throughout the entire subbinary range, not only below the
global envelope. At index two, top boundary moduli are already power
gaps; otherwise a subgroup extra completes the longer scaled prefix,
or both odd extras give a prefix-only rival. Index three is excluded by
the m-term coset cover. At index four, reflected fixed-prefix validity
directly gives a power gap downstairs, whose exponent shifts by two.

Dimensions five and six use the preceding arbitrary-multiplier global
bound and the already proved odd base theorems. No new tuple census or
unrestricted G1/G2/G3 hypothesis is used. The global envelope and actual
valuation separately bound the power-gap exponent, giving exact strata.

Coherence in the full modulus remains essential. Arbitrary independent
lift bits, prefix extraction from arbitrary tuples, and the unrestricted
global gates remain open; this closes the threshold gap for this class.
-/
import MinModulus.SITwoMultiplierBound

namespace MinModulus
open Finset

/-- From prefix length five onward, five times its fixed endpoint
dominates the entire two-step binary range. -/
theorem two_pow_add_two_le_five_mul_globalBound {m : ℕ} (hm : 5 ≤ m) :
    2 ^ (m + 2) ≤ 5 * globalBound m := by
  have hlin : 5 * m ≤ 2 ^ m := by
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih => rw [pow_succ']; omega
  have hlog := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  have hfive : 5 * 2 ^ Nat.log 2 m ≤ 2 ^ m := (Nat.mul_le_mul_left 5 hlog).trans hlin
  have hpowle : 2 ^ Nat.log 2 m ≤ 2 ^ m := by omega
  have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
  unfold globalBound
  omega

/-- In the full subbinary range, the divisor index is at most four
when the retained prefix has length at least five. -/
theorem divisor_le_four_of_valid_divisor_fixed_short_prefix_lt_two_pow
    {m d M : ℕ} [NeZero (d * M)] (hm : 5 ≤ m)
    (g : Fin (m + 2) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((d * a i.val : ℕ) : ZMod (d * M)))
    (hupper : d * M < 2 ^ (m + 2)) : d ≤ 4 := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne (d * M))
  have hMpos := Nat.pos_of_mul_pos_left hNpos
  letI : NeZero M := ⟨ne_of_gt hMpos⟩
  have hv := valid_fixed_of_valid_divisor_fixed_short_prefix g hg hprefix
  have hcard := Fintype.card_le_of_injective _ (validTuple_injective _ (validTuple_fixed_of_valid hv))
  simp only [Fintype.card_fin, ZMod.card] at hcard
  have hbound := (nmin_eq (by omega : 2 ≤ m)).2 ⟨by omega, hv⟩
  change globalBound m ≤ M at hbound
  have hratio := two_pow_add_two_le_five_mul_globalBound hm
  nlinarith

/-- If an extra completes the longer scaled prefix, its existing
power-gap theorem applies after moving that extra into the prefix. -/
theorem exists_power_gap_of_valid_divisor_short_prefix_and_next_lt_two_pow
    {m d M : ℕ} [NeZero (d * M)] (hm : 2 ≤ m)
    (g : Fin (m + 2) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((d * a i.val : ℕ) : ZMod (d * M)))
    (j : Fin (m + 2)) (hj : m ≤ j.val)
    (hnext : g j = ((d * a m : ℕ) : ZMod (d * M)))
    (hupper : d * M < 2 ^ (m + 2)) :
    ∃ t < m + 2, d * M = 2 ^ (m + 2) - 2 ^ t := by
  let x : Fin (m + 2) := (Fin.last m).castSucc
  let p := Equiv.swap j x
  have hfix (i : Fin m) : p i.castSucc.castSucc = i.castSucc.castSucc := by
    apply Equiv.swap_apply_of_ne_of_ne
    · intro heq
      have hv := congrArg Fin.val heq
      simp only [Fin.val_castSucc] at hv
      omega
    · intro heq
      have hv := congrArg Fin.val heq
      simp only [x, Fin.val_castSucc, Fin.val_last] at hv
      omega
  apply exists_power_gap_of_valid_divisor_fixed_prefix_lt_two_pow (by omega)
    (fun i ↦ g (p i)) (validTuple_embedding p.toEmbedding g hg) _ hupper
  intro i
  refine Fin.lastCases ?_ (fun k ↦ ?_) i
  · simpa [p, x] using hnext
  · rw [hfix, hprefix]
    rfl

/-- At index at least three, a subgroup extra is impossible even in
the larger subbinary range, by the reflected one-extra lower bound. -/
theorem not_validTuple_of_divisor_short_prefix_zero_extra_lt_two_pow
    {m d M : ℕ} [NeZero M] [NeZero (d * M)] (hm : 3 ≤ m) (hd : 3 ≤ d)
    (hupper : d * M < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (d * M))
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom d M (a i.val : ZMod M))
    (j : Fin (m + 2)) (hj : m ≤ j.val)
    (hjzero : ZMod.castHom (dvd_mul_right d M) (ZMod d) (g j) = 0) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨z, hz⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hjzero
  have hv := validTuple_fixed_extra_of_valid_scaled_short_prefix g hg hprefix j hj z hz.symm
  have hbound := global_lower_bound_of_valid_fixed_prefix (by omega) _ hv
    (by intro i; simp only [Fin.lastCases_castSucc])
  have hratio := two_pow_succ_le_three_mul_globalBound (by omega : 3 ≤ m + 1)
  nlinarith

/-- Index three cannot occur anywhere in the subbinary range once the
prefix has length at least five. The coset cover has enough room uniformly. -/
theorem not_validTuple_of_tripled_fixed_short_prefix_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 5 ≤ m)
    (hupper : 3 * M < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (3 * M))
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((3 * a i.val : ℕ) : ZMod (3 * M))) :
    ¬ ValidTuple g := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (3 * M) := ⟨by omega⟩
  intro hg
  have hpre : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom 3 M (a i.val : ZMod M) := by
    simpa only [zmodScaleHom_natCast] using hprefix
  have hM : M ≤ 3 * (2 ^ (m - 1) - 1) - (m - 2) := by
    have hp := three_mul_sub_one_le_mersenne_pred hm
    have hpow : 2 ^ (m + 2) = 8 * 2 ^ (m - 1) := by
      rw [show m + 2 = (m - 1) + 3 by omega, pow_add]; ring
    omega
  let π := ZMod.castHom (dvd_mul_right 3 M) (ZMod 3)
  rcases zmod_three_extra_cases (π (g (Fin.last m).castSucc)) (π (g (Fin.last (m + 1)))) with
    hx | hy | hdiff | hsum
  · exact not_validTuple_of_divisor_short_prefix_zero_extra_lt_two_pow (by omega) (by omega)
      hupper g hpre (Fin.last m).castSucc (by simp) hx hg
  · exact not_validTuple_of_divisor_short_prefix_zero_extra_lt_two_pow (by omega) (by omega)
      hupper g hpre (Fin.last (m + 1)) (by simp) hy hg
  · exact not_validTuple_of_scaled_short_prefix_extra_difference_zero (by omega) hM g hpre
      (by
        change π (g (Fin.last m).castSucc - g (Fin.last (m + 1))) = 0
        rw [map_sub, hdiff, sub_self]) hg
  · exact not_validTuple_of_scaled_short_prefix_extra_sum_zero (by omega)
      (by omega) g hpre (by simpa only [map_add] using hsum) hg

/-- In the doubled case, either a top binary residue is already a power
gap or an actual subgroup extra completes the longer scaled prefix. -/
theorem exists_power_gap_of_valid_doubled_fixed_short_prefix_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((2 * a i.val : ℕ) : ZMod (2 * M)))
    (hupper : 2 * M < 2 ^ (m + 2)) :
    ∃ t < m + 2, 2 * M = 2 ^ (m + 2) - 2 ^ t := by
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  have hpow : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by
    rw [show m + 2 = (m + 1) + 1 by omega, pow_succ']
  have hp := Nat.lt_two_pow_self (n := m + 1)
  have hMupper : M < 2 ^ (m + 1) := by omega
  by_cases hnear : M ≤ 2 ^ (m + 1) - 3
  · have hpre : ∀ i : Fin m, g i.castSucc.castSucc = zmodScaleHom 2 M (a i.val : ZMod M) := by
      simpa only [zmodScaleHom_natCast] using hprefix
    have hnext (j : Fin (m + 2)) (hj : m ≤ j.val)
        (hjzero : ZMod.castHom (dvd_mul_right 2 M) (ZMod 2) (g j) = 0) :
        g j = ((2 * a m : ℕ) : ZMod (2 * M)) := by
      obtain ⟨z, hz⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hjzero
      have hv := validTuple_fixed_extra_of_valid_scaled_short_prefix g hg hpre j hj z hz.symm
      have hfull := eq_fixed_of_valid_fixed_prefix_of_modulus_le (by omega) hnear _ hv
        (by intro i; simp only [Fin.lastCases_castSucc])
      have hznext : z = (a m : ZMod M) := by
        simpa only [Fin.lastCases_last, Fin.val_last] using congrFun hfull (Fin.last m)
      rw [← hz, hznext, zmodScaleHom_natCast]
    let π := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
    rcases zmod_two_extra_cases (π (g (Fin.last m).castSucc)) (π (g (Fin.last (m + 1)))) with hx | hy | hsum
    · exact exists_power_gap_of_valid_divisor_short_prefix_and_next_lt_two_pow (by omega) g hg
        hprefix (Fin.last m).castSucc (by simp) (hnext _ (by simp) hx) hupper
    · exact exists_power_gap_of_valid_divisor_short_prefix_and_next_lt_two_pow (by omega) g hg
        hprefix (Fin.last (m + 1)) (by simp) (hnext _ (by simp) hy) hupper
    · exact False.elim (not_validTuple_of_scaled_short_prefix_extra_sum_zero hm
        (modulus_le_two_extra_initial_cover hm (by omega)) g hpre
        (by simpa only [map_add] using hsum) hg)
  · by_cases htop : M = 2 ^ (m + 1) - 1
    · exact ⟨1, by omega, by norm_num; omega⟩
    · exact ⟨2, by omega, by norm_num; omega⟩

/-- At index four, reflected fixed-prefix validity already forces a
power gap: multiplying that gap by four shifts its exponent by two. -/
theorem exists_power_gap_of_valid_quadrupled_fixed_short_prefix_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (4 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((4 * a i.val : ℕ) : ZMod (4 * M)))
    (hupper : 4 * M < 2 ^ (m + 2)) :
    ∃ t < m + 2, 4 * M = 2 ^ (m + 2) - 2 ^ t := by
  have hpow : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; ring
  have hv := valid_fixed_of_valid_divisor_fixed_short_prefix g hg hprefix
  have hcard := Fintype.card_le_of_injective _ (validTuple_injective _ (validTuple_fixed_of_valid hv))
  simp only [Fintype.card_fin, ZMod.card] at hcard
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_fixed_lt_two_pow hm (by omega) (by omega) hv
  refine ⟨t + 2, by omega, ?_⟩
  simp only [hgap, Nat.mul_sub_left_distrib, pow_add]
  norm_num
  omega

/-- Divisor-scaled shorter prefixes force a power-gap modulus throughout
the subbinary range, uniformly from full dimension seven onward. -/
theorem exists_power_gap_of_valid_divisor_fixed_short_prefix_lt_two_pow
    {m d M : ℕ} [NeZero (d * M)] (hm : 5 ≤ m)
    (g : Fin (m + 2) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc.castSucc = ((d * a i.val : ℕ) : ZMod (d * M)))
    (hupper : d * M < 2 ^ (m + 2)) :
    ∃ t < m + 2, d * M = 2 ^ (m + 2) - 2 ^ t := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne (d * M))
  have hdpos := Nat.pos_of_mul_pos_right hNpos
  have hMpos := Nat.pos_of_mul_pos_left hNpos
  letI : NeZero M := ⟨ne_of_gt hMpos⟩
  have hd := divisor_le_four_of_valid_divisor_fixed_short_prefix_lt_two_pow hm g hg hprefix hupper
  interval_cases d
  · exact exists_power_gap_of_valid_fixed_short_prefix_lt_two_pow (by omega) g hg
      (by simpa using hprefix) hupper
  · exact exists_power_gap_of_valid_doubled_fixed_short_prefix_lt_two_pow (by omega) g hg hprefix hupper
  · exact False.elim (not_validTuple_of_tripled_fixed_short_prefix_lt_two_pow hm hupper g hprefix hg)
  · exact exists_power_gap_of_valid_quadrupled_fixed_short_prefix_lt_two_pow (by omega) g hg hprefix hupper

/-- Every coherent shorter-prefix multiplier forces a power-gap modulus
below `2^n`. The two small dimensions use the proved global/odd base bounds;
the all-dimensional part uses the justified full-subbinary index reduction. -/
theorem exists_power_gap_of_valid_scaled_fixed_short_prefix_lt_two_pow
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = c * (a i.val : ZMod N) + b)
    (hupper : N < 2 ^ (m + 2)) : ∃ t < m + 2, N = 2 ^ (m + 2) - 2 ^ t := by
  by_cases hm5 : 5 ≤ m
  · obtain ⟨d, hd, u, hu, hc⟩ := ZMod.eq_unit_mul_divisor c
    obtain ⟨M, hM⟩ := hd
    subst N
    obtain ⟨v, rfl⟩ := hu
    let φ : ZMod (d * M) ≃+ ZMod (d * M) :=
      (ZMod.AddAutEquivUnits (d * M)).symm (Additive.ofMul v)
    have hv := validTuple_sub_const (fun i ↦ g (e i))
      (validTuple_embedding e.toEmbedding g hg) b
    have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
    apply exists_power_gap_of_valid_divisor_fixed_short_prefix_lt_two_pow hm5
      (fun i ↦ φ.symm (g (e i) - b)) hw _ hupper
    intro i
    apply φ.injective
    rw [φ.apply_symm_apply, hprefix, add_sub_cancel_right, hc]
    change (v : ZMod (d * M)) * d * (a i.val : ZMod (d * M)) =
      (v : ZMod (d * M)) * ((d * a i.val : ℕ) : ZMod (d * M))
    push_cast
    ring
  · have hbound := global_lower_bound_of_valid_scaled_fixed_short_prefix hm g hg e c b hprefix
    have hcases : m = 3 ∨ m = 4 := by omega
    rcases hcases with rfl | rfl
    · norm_num [globalBound] at hbound hupper ⊢
      have hne29 : N ≠ 29 := by
        intro heq
        have hodd : Odd N := by rw [heq]; norm_num
        have := odd_min_five hodd g hg
        omega
      by_cases h28 : N = 28
      · exact ⟨2, by norm_num, by norm_num; omega⟩
      by_cases h30 : N = 30
      · exact ⟨1, by norm_num, by norm_num; omega⟩
      · exact ⟨0, by norm_num, by norm_num; omega⟩
    · norm_num [globalBound] at hbound hupper ⊢
      have hne61 : N ≠ 61 := by
        intro heq
        have hodd : Odd N := by rw [heq]; norm_num
        have := odd_min_six hodd g hg
        omega
      by_cases h60 : N = 60
      · exact ⟨2, by norm_num, by norm_num; omega⟩
      by_cases h62 : N = 62
      · exact ⟨1, by norm_num, by norm_num; omega⟩
      · exact ⟨0, by norm_num, by norm_num; omega⟩

/-- The exact stratum threshold for every coherent SI multiplier of
an n-2 prefix, including nonunits, with both extra entries arbitrary. -/
theorem stratum_lower_bound_of_valid_scaled_fixed_short_prefix
    {m s q : ℕ} (hm : 3 ≤ m) (hq : Odd q)
    (g : Fin (m + 2) → ZMod (2 ^ s * q)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod (2 ^ s * q))
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = c * (a i.val : ZMod (2 ^ s * q)) + b) :
    stratumBound (m + 2) s ≤ 2 ^ s * q := by
  have hqpos := hq.pos
  have hNpos : 0 < 2 ^ s * q := by positivity
  letI : NeZero (2 ^ s * q) := ⟨ne_of_gt hNpos⟩
  by_contra hnot
  have hgapPos : 0 < 2 ^ min s (Nat.log 2 (m + 2)) := by positivity
  have hupper : 2 ^ s * q < 2 ^ (m + 2) := by unfold stratumBound at hnot; omega
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_scaled_fixed_short_prefix_lt_two_pow
    hm g hg e c b hprefix hupper
  have hbound := global_lower_bound_of_valid_scaled_fixed_short_prefix hm g hg e c b hprefix
  have htlog : t ≤ Nat.log 2 (m + 2) := by
    apply (pow_le_pow_iff_right₀ (by omega : 1 < (2 : ℕ))).mp
    have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht.le
    rw [hgap] at hbound
    unfold globalBound at hbound
    omega
  have htwodvd : 2 ^ t ∣ 2 ^ s * q := by
    rw [hgap]
    exact Nat.dvd_sub (pow_dvd_pow 2 ht.le) (dvd_refl _)
  have hts : t ≤ s := by
    by_contra hc
    have hstep : 2 ^ s * 2 ∣ 2 ^ s * q := by
      rw [← pow_succ]
      exact (pow_dvd_pow 2 (by omega : s + 1 ≤ t)).trans htwodvd
    exact hq.not_two_dvd_nat (Nat.dvd_of_mul_dvd_mul_left (by positivity) hstep)
  have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (le_min hts htlog)
  unfold stratumBound at hnot
  omega

/-- The actual critical G1 range is excluded for every coherent
shorter-prefix multiplier, without assumptions about half witnesses. -/
theorem not_validTuple_of_critical_scaled_fixed_short_prefix
    {m s q : ℕ} (hm : 3 ≤ m) (hq : Odd q)
    (hcritical : 2 ^ s * q < stratumBound (m + 2) s)
    (g : Fin (m + 2) → ZMod (2 ^ s * q)) (e : Equiv.Perm (Fin (m + 2)))
    (c b : ZMod (2 ^ s * q))
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = c * (a i.val : ZMod (2 ^ s * q)) + b) :
    ¬ ValidTuple g := by
  intro hg
  exact (not_lt_of_ge
    (stratum_lower_bound_of_valid_scaled_fixed_short_prefix hm hq g hg e c b hprefix)) hcritical

/-- The odd G2 threshold holds for every coherent shorter-prefix
multiplier and two arbitrary extras, in every dimension at least five. -/
theorem odd_lower_bound_of_valid_scaled_fixed_short_prefix
    {m N : ℕ} (hm : 3 ≤ m) (hN : Odd N)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = c * (a i.val : ZMod N) + b) :
    2 ^ (m + 2) - 1 ≤ N := by
  have h := stratum_lower_bound_of_valid_scaled_fixed_short_prefix (s := 0) hm hN
  rw [show (2 : ℕ) ^ 0 * N = N by simp] at h
  simpa [stratumBound] using h g hg e c b hprefix

end MinModulus
