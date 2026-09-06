/-
# Power-gap rigidity and exact strata for arbitrary SI multipliers

For a valid tuple containing a coherent SI prefix of length n-1, even a
nonunit multiplier forces every modulus below 2^n to be a power gap.
Normalize the multiplier to a divisor d of N and reflect prefix validity
to modulus N/d. For n>=4, the fixed-set bound forces d<=2. The unit case
uses prefix completion; the doubled case inherits a power gap downstairs.
The n=3 case follows from the already proved global bound.

The global bound and odd-factor divisibility then bound the gap exponent
by both floor(log2 n) and the ambient valuation. Thus the exact stratum
threshold, critical G1 exclusion, and odd G2 threshold all hold for any
coherent SI multiplier. No unrestricted global gate is assumed or proved.
-/
import MinModulus.SIMultiplierBound

namespace MinModulus
open Finset

/-- A divisor-scaled valid prefix reflects to the fixed set at the smaller
modulus. No injectivity or nonzero-modulus hypothesis is needed. -/
theorem valid_fixed_of_valid_divisor_fixed_prefix
    {m d M : ℕ} (g : Fin (m + 1) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = ((d * a i.val : ℕ) : ZMod (d * M))) :
    Valid m M := by
  let e : Fin m ↪ Fin (m + 1) := ⟨Fin.castSucc, Fin.castSucc_injective m⟩
  have hsub := validTuple_embedding e g hg
  change ValidTuple (fun i : Fin m ↦ g i.castSucc) at hsub
  apply valid_fixed_of_validTuple
  apply validTuple_of_comp (zmodScaleHom d M)
  simpa only [zmodScaleHom_natCast, ← hprefix] using hsub

/-- From dimension three onwards, tripling the preceding endpoint reaches
the entire next binary range, not merely its global minimum. -/
theorem two_pow_succ_le_three_mul_globalBound {m : ℕ} (hm : 3 ≤ m) :
    2 ^ (m + 1) ≤ 3 * globalBound m := by
  have hsmall := succ_le_two_pow_pred m hm
  have hlog : Nat.log 2 m ≤ m - 2 := by
    have h := Nat.log_lt_of_lt_pow (by omega : m ≠ 0)
      (by omega : m < 2 ^ (m - 1))
    omega
  have hpowlog := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hlog
  have hp : 2 ^ m = 4 * 2 ^ (m - 2) := by
    calc
      2 ^ m = 2 ^ ((m - 2) + 2) := by congr 1; omega
      _ = 4 * 2 ^ (m - 2) := by rw [pow_add]; ring
  unfold globalBound
  rw [pow_succ']
  omega

/-- Below the binary range, a coherent SI block of at least three entries
can have subgroup index only one or two. -/
theorem divisor_le_two_of_valid_divisor_fixed_prefix_lt_two_pow
    {m d M : ℕ} [NeZero (d * M)] (hm : 3 ≤ m)
    (g : Fin (m + 1) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = ((d * a i.val : ℕ) : ZMod (d * M)))
    (hupper : d * M < 2 ^ (m + 1)) : d ≤ 2 := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne (d * M))
  have hMpos := Nat.pos_of_mul_pos_left hNpos
  letI : NeZero M := ⟨ne_of_gt hMpos⟩
  have hv := valid_fixed_of_valid_divisor_fixed_prefix g hg hprefix
  have hcard := Fintype.card_le_of_injective _
    (validTuple_injective _ (validTuple_fixed_of_valid hv))
  simp only [Fintype.card_fin, ZMod.card] at hcard
  have hbound := (nmin_eq (by omega : 2 ≤ m)).2 ⟨by omega, hv⟩
  change globalBound m ≤ M at hbound
  have hratio := two_pow_succ_le_three_mul_globalBound hm
  nlinarith

/-- The unit-prefix extension can occur below the binary range only at a
power gap. The two moduli above the prefix-completion range already have
this form. -/
theorem exists_power_gap_of_valid_fixed_prefix_lt_two_pow
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = (a i.val : ZMod N))
    (hupper : N < 2 ^ (m + 1)) : ∃ t < m + 1, N = 2 ^ (m + 1) - 2 ^ t := by
  by_cases hcover : N ≤ 2 ^ (m + 1) - 3
  · have hfull := eq_fixed_of_valid_fixed_prefix_of_modulus_le hm hcover g hg hprefix
    have hv := valid_fixed_of_validTuple (hfull ▸ hg)
    have hcard := Fintype.card_le_of_injective _ (validTuple_injective _ hg)
    simp only [Fintype.card_fin, ZMod.card] at hcard
    exact exists_power_gap_of_valid_fixed_lt_two_pow (by omega) (by omega) hupper hv
  · have hp : 8 ≤ 2 ^ (m + 1) := by
      simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : 3 ≤ m + 1)
    by_cases htop : N = 2 ^ (m + 1) - 1
    · exact ⟨0, by omega, by simpa using htop⟩
    · exact ⟨1, by omega, by norm_num; omega⟩

/-- For every divisor-scaled coherent prefix, validity below the binary
range forces a power-gap modulus. This conclusion does not require the
extra entry to complete the scaled SI set. -/
theorem exists_power_gap_of_valid_divisor_fixed_prefix_lt_two_pow
    {m d M : ℕ} [NeZero (d * M)] (hm : 2 ≤ m)
    (g : Fin (m + 1) → ZMod (d * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m, g i.castSucc = ((d * a i.val : ℕ) : ZMod (d * M)))
    (hupper : d * M < 2 ^ (m + 1)) :
    ∃ t < m + 1, d * M = 2 ^ (m + 1) - 2 ^ t := by
  by_cases hm2 : m = 2
  · subst m
    have hbound := global_lower_bound_of_valid_divisor_fixed_prefix (by omega) g hg hprefix
    norm_num [globalBound] at hbound hupper ⊢
    by_cases hN : d * M = 6
    · exact ⟨1, by omega, by norm_num; omega⟩
    · exact ⟨0, by omega, by norm_num; omega⟩
  have hm3 : 3 ≤ m := by omega
  have hd := divisor_le_two_of_valid_divisor_fixed_prefix_lt_two_pow hm3 g hg hprefix hupper
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne (d * M))
  have hdpos := Nat.pos_of_mul_pos_right hNpos
  have hMpos := Nat.pos_of_mul_pos_left hNpos
  letI : NeZero M := ⟨ne_of_gt hMpos⟩
  interval_cases d
  · exact exists_power_gap_of_valid_fixed_prefix_lt_two_pow hm g hg
      (by simpa using hprefix) (by simpa using hupper)
  · have hv := valid_fixed_of_valid_divisor_fixed_prefix g hg hprefix
    have hcard := Fintype.card_le_of_injective _
      (validTuple_injective _ (validTuple_fixed_of_valid hv))
    simp only [Fintype.card_fin, ZMod.card] at hcard
    have hMupper : M < 2 ^ m := by rw [pow_succ'] at hupper; omega
    obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_fixed_lt_two_pow
      hm3 (by omega) hMupper hv
    refine ⟨t + 1, by omega, ?_⟩
    rw [hgap, Nat.mul_sub_left_distrib, pow_succ', pow_succ']

/-- Power-gap rigidity for a coherent SI prefix with an arbitrary
multiplier, translation, reindexing, and extra entry. -/
theorem exists_power_gap_of_valid_scaled_fixed_prefix_lt_two_pow
    {m N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 1))) (c b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = c * (a i.val : ZMod N) + b)
    (hupper : N < 2 ^ (m + 1)) : ∃ t < m + 1, N = 2 ^ (m + 1) - 2 ^ t := by
  obtain ⟨d, hd, u, hu, hc⟩ := ZMod.eq_unit_mul_divisor c
  obtain ⟨M, hM⟩ := hd
  subst N
  obtain ⟨v, rfl⟩ := hu
  let φ : ZMod (d * M) ≃+ ZMod (d * M) :=
    (ZMod.AddAutEquivUnits (d * M)).symm (Additive.ofMul v)
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  apply exists_power_gap_of_valid_divisor_fixed_prefix_lt_two_pow hm
    (fun i ↦ φ.symm (g (e i) - b)) hw _ hupper
  intro i
  apply φ.injective
  rw [φ.apply_symm_apply, hprefix, add_sub_cancel_right, hc]
  change (v : ZMod (d * M)) * d * (a i.val : ZMod (d * M)) =
    (v : ZMod (d * M)) * ((d * a i.val : ℕ) : ZMod (d * M))
  push_cast
  ring

/-- Exact strata for every coherent SI multiplier, including nonunits.
The power-gap exponent is bounded by the global envelope and the actual
two-adic valuation, separately. -/
theorem stratum_lower_bound_of_valid_scaled_fixed_prefix
    {m s q : ℕ} (hm : 2 ≤ m) (hq : Odd q)
    (g : Fin (m + 1) → ZMod (2 ^ s * q)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 1))) (c b : ZMod (2 ^ s * q))
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = c * (a i.val : ZMod (2 ^ s * q)) + b) :
    stratumBound (m + 1) s ≤ 2 ^ s * q := by
  have hqpos := hq.pos
  have hNpos : 0 < 2 ^ s * q := by positivity
  letI : NeZero (2 ^ s * q) := ⟨ne_of_gt hNpos⟩
  by_contra hnot
  have hgapPos : 0 < 2 ^ min s (Nat.log 2 (m + 1)) := by positivity
  have hupper : 2 ^ s * q < 2 ^ (m + 1) := by unfold stratumBound at hnot; omega
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_scaled_fixed_prefix_lt_two_pow
    hm g hg e c b hprefix hupper
  have hbound := global_lower_bound_of_valid_scaled_fixed_prefix hm g hg e c b hprefix
  have htlog : t ≤ Nat.log 2 (m + 1) := by
    apply (pow_le_pow_iff_right₀ (by omega : 1 < (2 : ℕ))).mp
    have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht.le
    rw [hgap] at hbound
    unfold globalBound at hbound
    omega
  have htwodvd : 2 ^ t ∣ 2 ^ s * q := by
    rw [hgap]
    exact Nat.dvd_sub (pow_dvd_pow 2 ht.le) (dvd_refl _)
  have hts : t ≤ s := by
    by_contra hnot
    have hstep : 2 ^ s * 2 ∣ 2 ^ s * q := by
      rw [← pow_succ]
      exact (pow_dvd_pow 2 (by omega : s + 1 ≤ t)).trans htwodvd
    exact hq.not_two_dvd_nat (Nat.dvd_of_mul_dvd_mul_left (by positivity) hstep)
  have hle := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (le_min hts htlog)
  unfold stratumBound at hnot
  omega

/-- Direct critical-G1 exclusion for all coherent SI multipliers. -/
theorem not_validTuple_of_critical_scaled_fixed_prefix
    {m s q : ℕ} (hm : 2 ≤ m) (hq : Odd q)
    (hcritical : 2 ^ s * q < stratumBound (m + 1) s)
    (g : Fin (m + 1) → ZMod (2 ^ s * q)) (e : Equiv.Perm (Fin (m + 1)))
    (c b : ZMod (2 ^ s * q))
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = c * (a i.val : ZMod (2 ^ s * q)) + b) :
    ¬ ValidTuple g := by
  intro hg
  exact (not_lt_of_ge
    (stratum_lower_bound_of_valid_scaled_fixed_prefix hm hq g hg e c b hprefix)) hcritical

/-- The exact odd G2 threshold for a coherent SI prefix with any
multiplier, in every dimension at least three. -/
theorem odd_lower_bound_of_valid_scaled_fixed_prefix
    {m N : ℕ} (hm : 2 ≤ m) (hN : Odd N)
    (g : Fin (m + 1) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 1))) (c b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc) = c * (a i.val : ZMod N) + b) :
    2 ^ (m + 1) - 1 ≤ N := by
  have h := stratum_lower_bound_of_valid_scaled_fixed_prefix (s := 0) hm hN
  rw [show (2 : ℕ) ^ 0 * N = N by simp] at h
  simpa [stratumBound] using h g hg e c b hprefix

end MinModulus
