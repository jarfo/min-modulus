/-
# Full global and exact-stratum bounds for independent SI quotient prefixes

For every n>=3 and positive even modulus, a valid tuple whose actual half
quotient contains a unit-affine SI prefix of length n-1 satisfies the full
numerical global lower bound and every exact even-stratum threshold.
All original lift bits, extra values, and quotient affine transports are
allowed. Below 2^n, fixed-set validity at the same modulus is proved.

The induction preserves an actual full SI quotient prefix after odd-coset
halving. The other higher-even branch has an extracted coherent shorter
prefix. The first-even case has its proved Mersenne endpoint. An oversized
doubled child gap is excluded by the uniform independent-lift cover.
Only fixed dimension-three/four bases are kernel-enumerated; no census or
unrestricted G1/G2/G3 input is assumed. This is a modulus theorem, not an
affine classification or arbitrary-prefix extraction theorem.
-/
import MinModulus.SILiftSmallBases
import MinModulus.SILiftStructuredDescent

namespace MinModulus
open Finset

/-- Actual validity with a full independently lifted SI quotient prefix
implies fixed-set validity at the same subbinary modulus. The induction
preserves actual quotient structure through the odd-coset branch; an
oversized doubled gap is excluded by the proved uniform lift cover. -/
theorem valid_fixed_of_valid_si_lift_prefix_lt_two_pow :
    ∀ r : ℕ, 2 ≤ r → ∀ {M : ℕ} [NeZero M]
      (g : Fin (r + 1) → ZMod (2 * M)), ValidTuple g →
      (∀ i : Fin r, ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g i.castSucc) =
        (a i.val : ZMod M)) →
      2 * M < 2 ^ (r + 1) → Valid (r + 1) (2 * M) := by
  intro r
  induction r with
  | zero => intro hr; omega
  | succ r ih =>
    intro hr M inst g hg hprefix hupper
    by_cases hr1 : r = 1
    · subst r
      exact valid_fixed_three_of_valid_subbinary_even_tuple g hg hupper
    by_cases hr2 : r = 2
    · subst r
      exact valid_fixed_four_of_valid_subbinary_si_lift_prefix g hg hprefix hupper
    have hr3 : 3 ≤ r := by omega
    have hMpos := Nat.pos_of_ne_zero (NeZero.ne M)
    rcases Nat.even_or_odd M with hMeven | hModd
    · obtain ⟨L, hL⟩ := hMeven
      have hM : M = 2 * L := by omega
      clear hL
      subst M
      have hLpos : 0 < L := by omega
      letI : NeZero L := ⟨by omega⟩
      have hchildUpper : 2 * L < 2 ^ (r + 1) := by
        have hp : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by rw [show r + 2 = r + 1 + 1 by omega, pow_succ']
        change 2 * (2 * L) < 2 ^ (r + 2) at hupper
        omega
      rcases structured_half_or_coherent_short_prefix_of_even_si_lifts hr3 hupper g hg hprefix with
        ⟨h, hvalid, hpref⟩ | ⟨c, b, hcoh⟩
      · have hfixed := ih (by omega) h hvalid hpref hchildUpper
        obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_fixed_lt_two_pow
          (by omega : 3 ≤ r + 1) (by omega) hchildUpper hfixed
        have hb := (nmin_eq (by omega : 2 ≤ r + 1)).2 ⟨by omega, hfixed⟩
        have hlog := Nat.pow_log_le_self 2 (by omega : r + 1 ≠ 0)
        have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) ht.le
        have htbound : 2 ^ t ≤ r + 1 := by
          change globalBound (r + 1) ≤ 2 * L at hb
          unfold globalBound at hb
          rw [hgap] at hb
          omega
        have htpos : 1 ≤ t := by
          by_contra h
          have ht0 : t = 0 := by omega
          rw [ht0, pow_zero, pow_succ'] at hgap
          have hpos : 0 < 2 ^ r := by positivity
          omega
        by_cases hbudget : 2 ^ (t + 1) ≤ r + 2
        · have hparent : 2 * (2 * L) = 2 ^ (r + 2) - 2 ^ (t + 1) := by
            have hp : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by rw [show r + 2 = r + 1 + 1 by omega, pow_succ']
            have hpt : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ']
            omega
          change Valid (r + 2) (2 * (2 * L))
          rw [hparent]
          exact valid_gap (by omega) hbudget
        · exact False.elim (not_validTuple_of_si_lift_prefix
            (by omega : 2 ≤ r + 1) htpos htbound (by omega) hgap g hprefix hg)
      · exact valid_fixed_of_valid_scaled_fixed_short_prefix_lt_two_pow hr3 g hg
          (Equiv.refl _) c b hcoh hupper
    · have hM := half_eq_mersenne_of_valid_subbinary_odd_quotient_affine_si_prefix
        hr3 hModd hupper g hg (Equiv.refl _) (AddEquiv.refl _) 0
        (by intro i; simpa only [Equiv.refl_apply, AddEquiv.refl_apply, add_zero] using hprefix i)
      have hparent : 2 * M = 2 ^ (r + 2) - 2 ^ 1 := by
        have hp : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by rw [show r + 2 = r + 1 + 1 by omega, pow_succ']
        have hpos : 0 < 2 ^ (r + 1) := by positivity
        norm_num only [pow_one]
        omega
      change Valid (r + 2) (2 * M)
      rw [hparent]
      exact valid_gap (by omega) (by norm_num)

/-- Quotient affine normalization preserves the fixed-validity conclusion.
The original lift bits and extra are arbitrary, and the resulting theorem
is about the modulus, not an affine classification of the original tuple. -/
theorem valid_fixed_of_valid_quotient_affine_si_prefix_lt_two_pow
    {r M : ℕ} [NeZero M] (hr : 2 ≤ r)
    (g : Fin (r + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (r + 1))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin r, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b)
    (hupper : 2 * M < 2 ^ (r + 1)) : Valid (r + 1) (2 * M) := by
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left M 2) φ
  let zero : Fin (r + 1) := (⟨0, by omega⟩ : Fin r).castSucc
  let B := g (e zero)
  let w := fun i ↦ Φ.symm (g (e i) - B)
  have hB : ZMod.castHom (dvd_mul_left M 2) (ZMod M) B = b := by
    simpa only [a, pow_zero, Nat.sub_self, Nat.cast_zero, map_zero, zero_add] using hprefix ⟨0, by omega⟩
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) B
  have hw : ValidTuple w := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  apply valid_fixed_of_valid_si_lift_prefix_lt_two_pow r hr w hw _ hupper
  intro i
  apply φ.injective
  rw [← hΦ, Φ.apply_symm_apply, map_sub, hprefix, hB, add_sub_cancel_right]

/-- Unconditional numerical global lower bound for every independent
full unit-affine SI half-quotient prefix, all positive even moduli and
all n>=3. No unrestricted G1, G2, or G3 theorem is assumed. -/
theorem global_lower_bound_of_valid_quotient_affine_si_prefix
    {r M : ℕ} [NeZero M] (hr : 2 ≤ r)
    (g : Fin (r + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (r + 1))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin r, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b) : globalBound (r + 1) ≤ 2 * M := by
  by_cases hupper : 2 * M < 2 ^ (r + 1)
  · have hv := valid_fixed_of_valid_quotient_affine_si_prefix_lt_two_pow hr g hg e φ b hprefix hupper
    have hM := Nat.pos_of_ne_zero (NeZero.ne M)
    exact (nmin_eq (by omega : 2 ≤ r + 1)).2 ⟨by omega, hv⟩
  · exact (Nat.sub_le _ _).trans (le_of_not_gt hupper)

/-- Independent full unit-affine half-quotient prefixes satisfy every exact
even-stratum threshold, not only the global envelope or G3 endpoint. -/
theorem stratum_lower_bound_of_valid_quotient_affine_si_prefix
    {r M s q : ℕ} [NeZero M] (hr : 2 ≤ r) (hq : Odd q)
    (hN : 2 * M = 2 ^ s * q)
    (g : Fin (r + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (r + 1))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin r, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b) : stratumBound (r + 1) s ≤ 2 * M := by
  by_cases hupper : 2 * M < 2 ^ (r + 1)
  · have hv := valid_fixed_of_valid_quotient_affine_si_prefix_lt_two_pow hr g hg e φ b hprefix hupper
    have hv' : Valid (r + 1) (2 ^ s * q) := hN ▸ hv
    have hb := stratum_lower_bound_of_valid_fixed (by omega : 3 ≤ r + 1) hq hv'
    simpa only [← hN] using hb
  · exact (Nat.sub_le _ _).trans (le_of_not_gt hupper)

/-- The original even modulus is a fixed admissible power gap throughout
the subbinary full quotient-prefix class. This does not classify its lifts. -/
theorem exists_admissible_power_gap_of_valid_quotient_affine_si_prefix
    {r M : ℕ} [NeZero M] (hr : 2 ≤ r)
    (g : Fin (r + 1) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (r + 1))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin r, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b)
    (hupper : 2 * M < 2 ^ (r + 1)) :
    ∃ t < r + 1, 2 ^ t ≤ r + 1 ∧ 2 * M = 2 ^ (r + 1) - 2 ^ t := by
  have hv := valid_fixed_of_valid_quotient_affine_si_prefix_lt_two_pow hr g hg e φ b hprefix hupper
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_fixed_lt_two_pow (by omega) (by omega) hupper hv
  have hb := global_lower_bound_of_valid_quotient_affine_si_prefix hr g hg e φ b hprefix
  have hlog := Nat.pow_log_le_self 2 (by omega : r + 1 ≠ 0)
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) ht.le
  refine ⟨t, ht, ?_, hgap⟩
  unfold globalBound at hb
  rw [hgap] at hb
  omega

/-- Direct critical-range consumer for arbitrary original lift bits.
The unrestricted G1 residual therefore contains no full unit-affine SI
half-quotient prefix in any dimension n>=3 or any even stratum. -/
theorem not_validTuple_of_critical_quotient_affine_si_prefix
    {r M s q : ℕ} [NeZero M] (hr : 2 ≤ r) (hq : Odd q)
    (hN : 2 * M = 2 ^ s * q) (hcritical : 2 * M < stratumBound (r + 1) s)
    (g : Fin (r + 1) → ZMod (2 * M))
    (e : Equiv.Perm (Fin (r + 1))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin r, ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b) : ¬ ValidTuple g := by
  intro hg
  exact (not_lt_of_ge (stratum_lower_bound_of_valid_quotient_affine_si_prefix
    hr hq hN g hg e φ b hprefix)) hcritical

end MinModulus
