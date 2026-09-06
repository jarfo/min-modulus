/-
# Full global and exact-stratum bounds for arbitrary SI quotient multipliers

For every n>=5, a valid tuple with a full SI half-quotient prefix under
ANY multiplier satisfies the global bound and every even-stratum bound.
All original lift bits, extra entries, reindexings, and translations are
allowed. Below 2^n, fixed-set validity holds at the same modulus.

Normalize the quotient multiplier to a divisor d of the half modulus and
divide the actual retained prefix by d. It is valid and has a unit SI
half-quotient prefix. The proved unit-class bound forces d<=2 below the
binary range. At d=2 the child's fixed-valid power gap produces an actual
quotient collision at the terminal prefix coordinate; the existing
collision deletion theorem supplies the full original-modulus conclusion.

No classification of the original lifts, external census, or unrestricted
G1/G2/G3 premise is used. Arbitrary-prefix extraction remains open.
-/
import MinModulus.SILiftFullBound

namespace MinModulus
open Finset

/-- Divide an independently lifted divisor-scaled prefix by its subgroup
index. The actual divided prefix is valid and has unit SI quotient data. -/
theorem exists_valid_divided_si_lift_prefix
    {m d L : ℕ} [NeZero d] [NeZero L]
    (g : Fin (m + 1) → ZMod (d * (2 * L))) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin m,
      ZMod.castHom (show d * L ∣ d * (2 * L) from ⟨2, by ring⟩) (ZMod (d * L))
        (g i.castSucc) = ((d * a i.val : ℕ) : ZMod (d * L))) :
    ∃ h : Fin m → ZMod (2 * L), ValidTuple h ∧
      ∀ i, ZMod.castHom (dvd_mul_left L 2) (ZMod L) (h i) = (a i.val : ZMod L) := by
  have hd := Nat.pos_of_ne_zero (NeZero.ne d)
  have hL := Nat.pos_of_ne_zero (NeZero.ne L)
  letI : NeZero (d * (2 * L)) := ⟨by positivity⟩
  let π := ZMod.castHom (show d * L ∣ d * (2 * L) from ⟨2, by ring⟩) (ZMod (d * L))
  let ρ := ZMod.castHom (dvd_mul_right d L) (ZMod d)
  let σ := ZMod.castHom (dvd_mul_right d (2 * L)) (ZMod d)
  have hzero (i : Fin m) : σ (g i.castSucc) = 0 := by
    have heq := congrArg ρ (hprefix i)
    have hcomp : ρ.comp π = σ := ZMod.castHom_comp _ _
    change (ρ.comp π) (g i.castSucc) = _ at heq
    rw [hcomp] at heq
    simpa [ρ, Nat.cast_mul] using heq
  choose h hh using fun i : Fin m ↦
    exists_zmodScaleHom_eq_of_castHom_eq_zero (g i.castSucc) (hzero i)
  refine ⟨h, ?_, ?_⟩
  · apply validTuple_of_comp (zmodScaleHom d (2 * L))
    have hv := validTuple_embedding
      (⟨Fin.castSucc, Fin.castSucc_injective m⟩ : Fin m ↪ Fin (m + 1)) g hg
    change ValidTuple (fun i : Fin m ↦ g i.castSucc) at hv
    simpa only [hh] using hv
  · intro i
    have heq := hprefix i
    rw [← hh i, ← ZMod.natCast_zmod_val (h i), zmodScaleHom_natCast, map_natCast] at heq
    have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp heq
    rw [Nat.mul_mod_mul_left, Nat.mul_mod_mul_left] at hmod
    have hsmall := Nat.mul_left_cancel hd hmod
    rw [← ZMod.natCast_zmod_val (h i), map_natCast, ZMod.natCast_eq_natCast_iff']
    exact hsmall

/-- A full independently lifted divisor-scaled quotient prefix forces
fixed-set validity at the original subbinary modulus. Index two is
resolved by an actual quotient collision, not a classification premise. -/
theorem valid_fixed_of_valid_divisor_si_lift_prefix_lt_two_pow
    {m d L : ℕ} [NeZero d] [NeZero L] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (d * (2 * L))) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1),
      ZMod.castHom (show d * L ∣ d * (2 * L) from ⟨2, by ring⟩) (ZMod (d * L))
        (g i.castSucc) = ((d * a i.val : ℕ) : ZMod (d * L)))
    (hupper : d * (2 * L) < 2 ^ (m + 2)) : Valid (m + 2) (d * (2 * L)) := by
  have hd := Nat.pos_of_ne_zero (NeZero.ne d)
  have hL := Nat.pos_of_ne_zero (NeZero.ne L)
  letI : NeZero (2 * L) := ⟨by positivity⟩
  obtain ⟨h, hv, hp⟩ := exists_valid_divided_si_lift_prefix g hg hprefix
  have hb := global_lower_bound_of_valid_quotient_affine_si_prefix
    (by omega : 2 ≤ m) h hv (Equiv.refl _) (AddEquiv.refl _) 0
    (by intro i; simpa using hp i.castSucc)
  have hratio := two_pow_succ_le_three_mul_globalBound (by omega : 3 ≤ m + 1)
  have hdsmall : d ≤ 2 := by nlinarith
  interval_cases d
  · let f : Fin (m + 2) → ZMod (2 * L) := fun i ↦ ((g i).val : ZMod (2 * L))
    have hf : ∀ i, zmodScaleHom 1 (2 * L) (f i) = g i := by
      intro i
      rw [zmodScaleHom_natCast, show 1 * (g i).val = (g i).val by omega,
        ZMod.natCast_zmod_val]
    have hfv : ValidTuple f := by
      apply validTuple_of_comp (zmodScaleHom 1 (2 * L))
      simpa only [hf] using hg
    have hfp : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left L 2) (ZMod L)
        (f i.castSucc) = (a i.val : ZMod L) := by
      intro i
      have hpi := hprefix i
      rw [← ZMod.natCast_zmod_val (g i.castSucc), map_natCast] at hpi
      change ZMod.castHom _ _ (((g i.castSucc).val : ℕ) : ZMod (2 * L)) = _
      rw [map_natCast]
      apply (ZMod.natCast_eq_natCast_iff' _ _ _).mpr
      have hmod := (ZMod.natCast_eq_natCast_iff' _ _ _).mp hpi
      simpa only [one_mul] using hmod
    have hresult := valid_fixed_of_valid_si_lift_prefix_lt_two_pow (m + 1) (by omega)
      f hfv hfp (by simpa only [one_mul] using hupper)
    simpa only [one_mul] using hresult
  · have hchildUpper : 2 * L < 2 ^ (m + 1) := by
      rw [show m + 2 = m + 1 + 1 by omega, pow_succ'] at hupper
      omega
    have hfixed := valid_fixed_of_valid_si_lift_prefix_lt_two_pow m (by omega) h hv
      (fun i ↦ hp i.castSucc) hchildUpper
    obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_fixed_lt_two_pow
      (by omega : 3 ≤ m + 1) (by omega) hchildUpper hfixed
    have htpos : 1 ≤ t := by
      by_contra hnot
      have htzero : t = 0 := by omega
      rw [htzero, pow_zero, pow_succ'] at hgap
      have hpow : 0 < 2 ^ m := by positivity
      omega
    let j : Fin (m + 2) := (Fin.last m).castSucc
    let k : Fin (m + 2) := (⟨t - 1, by omega⟩ : Fin (m + 1)).castSucc
    have hneq : k ≠ (Equiv.refl _) j := by
      intro heq
      have heq' := congrArg Fin.val heq
      simp only [k, j, Equiv.refl_apply, Fin.val_castSucc, Fin.val_last] at heq'
      omega
    have hcollision : ZMod.castHom (dvd_mul_left (2 * L) 2) (ZMod (2 * L)) (g k) =
        ZMod.castHom (dvd_mul_left (2 * L) 2) (ZMod (2 * L)) (g ((Equiv.refl _) j)) := by
      change ZMod.castHom _ _ (g (⟨t - 1, by omega⟩ : Fin (m + 1)).castSucc) =
        ZMod.castHom _ _ (g (Fin.last m).castSucc)
      rw [hprefix, hprefix]
      have hpw := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht.le
      have ha : 2 * a m = 2 * a (t - 1) + 2 * L := by
        have hpt : 2 ^ t = 2 * 2 ^ (t - 1) := by rw [← pow_succ']; congr 1; omega
        have hmpos : 0 < 2 ^ m := by positivity
        have htpos' : 0 < 2 ^ (t - 1) := by positivity
        unfold a
        rw [pow_succ'] at hgap
        omega
      have hc := congrArg (fun v : ℕ ↦ (v : ZMod (2 * L))) ha
      simpa only [Fin.val_last, Nat.cast_add, ZMod.natCast_self, add_zero] using hc.symm
    obtain ⟨E, hret, hpref⟩ := exists_valid_half_quotient_scaled_short_prefix_of_tail_collision
      g hg (Equiv.refl _) 2 0 j (by simp [j]) k hneq hcollision
      (by intro i; simpa only [Equiv.refl_apply, Fin.val_castSucc, add_zero, Nat.cast_mul, Nat.cast_ofNat]
        using hprefix i.castSucc)
    exact valid_fixed_of_valid_quotient_scaled_short_prefix_lt_two_pow hm g hg E 2 0
      hret hpref hupper

/-- All quotient multipliers, including nonunits, are allowed together
with arbitrary original lift bits and the extra entry. -/
theorem valid_fixed_of_valid_quotient_scaled_si_prefix_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = c * (a i.val : ZMod M) + b)
    (hupper : 2 * M < 2 ^ (m + 2)) : Valid (m + 2) (2 * M) := by
  obtain ⟨d, hd, u, hu, hc⟩ := ZMod.eq_unit_mul_divisor c
  obtain ⟨L, hL⟩ := hd
  subst M
  have hMpos := Nat.pos_of_ne_zero (NeZero.ne (d * L))
  letI : NeZero d := ⟨by intro hz; simp [hz] at hMpos⟩
  letI : NeZero L := ⟨by intro hz; simp [hz] at hMpos⟩
  letI : NeZero (2 * (d * L)) := ⟨by positivity⟩
  obtain ⟨v, rfl⟩ := hu
  let φ : ZMod (d * L) ≃+ ZMod (d * L) :=
    (ZMod.AddAutEquivUnits (d * L)).symm (Additive.ofMul v)
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left (d * L) 2) φ
  let z : Fin (m + 1) := ⟨0, by omega⟩
  let B := g (e z.castSucc)
  let w := fun i ↦ Φ.symm (g (e i) - B)
  have hB : ZMod.castHom (dvd_mul_left (d * L) 2) (ZMod (d * L)) B = b := by
    simpa only [z, a, pow_zero, Nat.sub_self, Nat.cast_zero, mul_zero, zero_add]
      using hprefix z
  have hv := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) B
  have hw : ValidTuple w := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  have hp : ∀ i : Fin (m + 1),
      ZMod.castHom (dvd_mul_left (d * L) 2) (ZMod (d * L)) (w i.castSucc) =
        ((d * a i.val : ℕ) : ZMod (d * L)) := by
    intro i
    apply φ.injective
    rw [← hΦ]
    change ZMod.castHom _ _ (Φ (Φ.symm (g (e i.castSucc) - B))) = _
    rw [Φ.apply_symm_apply, map_sub, hprefix, hB, add_sub_cancel_right, hc]
    change (v : ZMod (d * L)) * d * (a i.val : ZMod (d * L)) =
      (v : ZMod (d * L)) * ((d * a i.val : ℕ) : ZMod (d * L))
    push_cast
    ring
  have hN : 2 * (d * L) = d * (2 * L) := by ring
  have hfinish : ∀ N : ℕ, N = d * (2 * L) → ∀ (hdiv : d * L ∣ N)
      (w : Fin (m + 2) → ZMod N), ValidTuple w →
      (∀ i : Fin (m + 1), ZMod.castHom hdiv (ZMod (d * L))
        (w i.castSucc) = ((d * a i.val : ℕ) : ZMod (d * L))) →
      N < 2 ^ (m + 2) → Valid (m + 2) N := by
    intro N heq
    subst N
    intro hdiv w hw hp hupper
    exact valid_fixed_of_valid_divisor_si_lift_prefix_lt_two_pow hm w hw hp hupper
  exact hfinish _ hN _ w hw hp hupper

/-- Full numerical global bound with independent half-modulus lift bits
and ANY quotient multiplier, every n>=5. -/
theorem global_lower_bound_of_valid_quotient_scaled_si_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = c * (a i.val : ZMod M) + b) :
    globalBound (m + 2) ≤ 2 * M := by
  by_cases hupper : 2 * M < 2 ^ (m + 2)
  · have hv := valid_fixed_of_valid_quotient_scaled_si_prefix_lt_two_pow hm g hg e c b hprefix hupper
    have hM := Nat.pos_of_ne_zero (NeZero.ne M)
    exact (nmin_eq (by omega : 2 ≤ m + 2)).2 ⟨by omega, hv⟩
  · exact (Nat.sub_le _ _).trans (le_of_not_gt hupper)

/-- Exact even-stratum thresholds hold for the same arbitrary multipliers
and original lift bits, without a global gate assumption. -/
theorem stratum_lower_bound_of_valid_quotient_scaled_si_prefix
    {m M s q : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd q)
    (hN : 2 * M = 2 ^ s * q)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = c * (a i.val : ZMod M) + b) :
    stratumBound (m + 2) s ≤ 2 * M := by
  by_cases hupper : 2 * M < 2 ^ (m + 2)
  · have hv := valid_fixed_of_valid_quotient_scaled_si_prefix_lt_two_pow hm g hg e c b hprefix hupper
    have hv' : Valid (m + 2) (2 ^ s * q) := hN ▸ hv
    simpa only [← hN] using stratum_lower_bound_of_valid_fixed (by omega) hq hv'
  · exact (Nat.sub_le _ _).trans (le_of_not_gt hupper)

/-- Fixed admissible power-gap rigidity for independent full quotient
prefixes under any multiplier; no classification of the lifts is asserted. -/
theorem exists_admissible_power_gap_of_valid_quotient_scaled_si_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = c * (a i.val : ZMod M) + b)
    (hupper : 2 * M < 2 ^ (m + 2)) :
    ∃ t < m + 2, 2 ^ t ≤ m + 2 ∧ 2 * M = 2 ^ (m + 2) - 2 ^ t := by
  have hv := valid_fixed_of_valid_quotient_scaled_si_prefix_lt_two_pow hm g hg e c b hprefix hupper
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_fixed_lt_two_pow (by omega) (by omega) hupper hv
  have hb := global_lower_bound_of_valid_quotient_scaled_si_prefix hm g hg e c b hprefix
  have hlog := Nat.pow_log_le_self 2 (by omega : m + 2 ≠ 0)
  have hpow := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht.le
  refine ⟨t, ht, ?_, hgap⟩
  unfold globalBound at hb
  rw [hgap] at hb
  omega

/-- No critical tuple in any even stratum contains a full independently
lifted SI quotient prefix, under ANY multiplier, in dimensions n>=5. -/
theorem not_validTuple_of_critical_quotient_scaled_si_prefix
    {m M s q : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd q)
    (hN : 2 * M = 2 ^ s * q) (hcritical : 2 * M < stratumBound (m + 2) s)
    (g : Fin (m + 2) → ZMod (2 * M))
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = c * (a i.val : ZMod M) + b) : ¬ ValidTuple g := by
  intro hg
  exact (not_lt_of_ge (stratum_lower_bound_of_valid_quotient_scaled_si_prefix
    hm hq hN g hg e c b hprefix)) hcritical

end MinModulus
