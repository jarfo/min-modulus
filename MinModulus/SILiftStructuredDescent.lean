/-
# Actual full SI quotient-prefix preservation through coset halving
-/
import MinModulus.SILiftOddComplete

namespace MinModulus
open Finset

/-- Equality after doubling in ZMod (2*M) cancels in the quotient ZMod M,
even when M itself is even. -/
theorem castHom_eq_of_two_nsmul_eq
    {M : ℕ} [NeZero M] (x y : ZMod (2 * M)) (h : 2 • x = 2 • y) :
    ZMod.castHom (dvd_mul_left M 2) (ZMod M) x =
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) y := by
  have hz : 2 • (x - y) = 0 := by rw [smul_sub, h, sub_self]
  have hd : 2 * M ∣ 2 * (x - y).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val, nsmul_eq_mul] using hz
  have hM : M ∣ (x - y).val := (Nat.mul_dvd_mul_iff_left (by decide : 0 < (2 : ℕ))).mp hd
  have hp : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (x - y) = 0 := by
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff]
    exact hM
  rw [map_sub] at hp
  exact sub_eq_zero.mp hp

/-- Actual odd-coset halving preserves a full SI prefix in the NEXT half
quotient. This constructs the smaller tuple and proves its prefix, rather
than replacing the descent step by a new structural assumption. -/
theorem exists_valid_si_lift_prefix_of_odd_coset_halving
    {m L : ℕ} [NeZero L]
    (g : Fin (m + 2) → ZMod (2 * (2 * L))) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1),
      ZMod.castHom (dvd_mul_left (2 * L) 2) (ZMod (2 * L)) (g i.castSucc) =
        (a i.val : ZMod (2 * L)))
    (hx : ZMod.castHom (dvd_mul_right 2 (2 * L)) (ZMod 2)
      (g (Fin.last (m + 1))) = 1) :
    ∃ h : Fin (m + 1) → ZMod (2 * L), ValidTuple h ∧
      ∀ i : Fin m, ZMod.castHom (dvd_mul_left L 2) (ZMod L) (h i.castSucc) =
        (a i.val : ZMod L) := by
  have hL := Nat.pos_of_ne_zero (NeZero.ne L)
  letI : NeZero (2 * L) := ⟨by omega⟩
  letI : NeZero (2 * (2 * L)) := ⟨by omega⟩
  let π := ZMod.castHom (dvd_mul_left (2 * L) 2) (ZMod (2 * L))
  let ρ := ZMod.castHom (dvd_mul_right 2 L) (ZMod 2)
  let σ := ZMod.castHom (dvd_mul_right 2 (2 * L)) (ZMod 2)
  have hcomp (x : ZMod (2 * (2 * L))) : ρ (π x) = σ x := by
    change (ρ.comp π) x = σ x
    rw [show ρ.comp π = σ from ZMod.castHom_comp _ _]
  have hodd (i : Fin (m + 1)) : σ (g i.succ) = 1 := by
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · exact hx
    · change σ (g k.succ.castSucc) = 1
      rw [← hcomp, hprefix, map_natCast]
      have ha : a (k.val + 1) + 1 = 2 ^ (k.val + 1) := by
        unfold a
        have hp : 0 < 2 ^ (k.val + 1) := by positivity
        omega
      have hh := congrArg (fun r : ℕ ↦ (r : ZMod 2)) ha
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat,
        show (2 : ZMod 2) = 0 by decide, zero_pow (by omega : k.val + 1 ≠ 0)] at hh
      have h2 : (1 : ZMod 2) + 1 = 0 := by decide
      change (a (k.val + 1) : ZMod 2) = 1
      linear_combination hh - h2
  let v : Fin (m + 1) → ZMod (2 * (2 * L)) := fun i ↦ g i.succ - 1
  have hv : ValidTuple v := validTuple_sub_const _
    (validTuple_embedding ⟨Fin.succ, Fin.succ_injective (m + 1)⟩ g hg) 1
  have hev (i : Fin (m + 1)) : Even (v i).val := by
    have hzero : σ (v i) = 0 := by rw [map_sub, hodd, map_one, sub_self]
    rw [ZMod.castHom_apply, ← ZMod.natCast_val, ZMod.natCast_eq_zero_iff] at hzero
    exact even_iff_two_dvd.mpr hzero
  let h : Fin (m + 1) → ZMod (2 * L) := fun i ↦ (((v i).val / 2 : ℕ) : ZMod (2 * L))
  have hvalid : ValidTuple h := validTuple_half_of_even_values v hv hev
  have hd (i : Fin (m + 1)) : zmodDoubleHom (2 * L) (h i) = v i := by
    rw [zmodDoubleHom_natCast, Nat.mul_div_cancel' (hev i).two_dvd, ZMod.natCast_zmod_val]
  have htwo (i : Fin (m + 1)) : 2 • h i = π (v i) := by
    calc
      _ = π (zmodDoubleHom (2 * L) (h i)) := by
        rw [← ZMod.natCast_zmod_val (h i), zmodDoubleHom_natCast, map_natCast]
        simp only [nsmul_eq_mul, Nat.cast_mul, Nat.cast_ofNat]
      _ = _ := by rw [hd]
  refine ⟨h, hvalid, ?_⟩
  intro i
  suffices hh : 2 • h i.castSucc = 2 • (a i.val : ZMod (2 * L)) by
    simpa only [map_natCast] using castHom_eq_of_two_nsmul_eq _ _ hh
  rw [htwo]
  change π (g i.succ.castSucc - 1) = 2 • (a i.val : ZMod (2 * L))
  rw [map_sub, hprefix, map_one]
  have ha : a (i.val + 1) = 2 * a i.val + 1 := by
    unfold a
    have hp : 0 < 2 ^ i.val := by positivity
    rw [pow_succ']; omega
  change (a (i.val + 1) : ZMod (2 * L)) - 1 = 2 • (a i.val : ZMod (2 * L))
  rw [ha]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, nsmul_eq_mul, add_sub_cancel_right]

/-- The higher-even split retains the actual next-quotient prefix in the
coset branch, or extracts a coherent shorter prefix upstairs. -/
theorem structured_half_or_coherent_short_prefix_of_even_si_lifts
    {m L : ℕ} [NeZero L] (hm : 3 ≤ m)
    (hupper : 2 * (2 * L) < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (2 * (2 * L))) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1),
      ZMod.castHom (dvd_mul_left (2 * L) 2) (ZMod (2 * L)) (g i.castSucc) =
        (a i.val : ZMod (2 * L))) :
    (∃ h : Fin (m + 1) → ZMod (2 * L), ValidTuple h ∧
      ∀ i : Fin m, ZMod.castHom (dvd_mul_left L 2) (ZMod L) (h i.castSucc) =
        (a i.val : ZMod L)) ∨
    ∃ c b : ZMod (2 * (2 * L)), ∀ i : Fin m,
      g i.castSucc.castSucc = c * (a i.val : ZMod (2 * (2 * L))) + b := by
  have hL := Nat.pos_of_ne_zero (NeZero.ne L)
  letI : NeZero (2 * L) := ⟨by omega⟩
  let π := ZMod.castHom (dvd_mul_left (2 * L) 2) (ZMod (2 * L))
  let ρ := ZMod.castHom (dvd_mul_right 2 L) (ZMod 2)
  let σ := ZMod.castHom (dvd_mul_right 2 (2 * L)) (ZMod 2)
  have hcomp (x : ZMod (2 * (2 * L))) : ρ (π x) = σ x := by
    change (ρ.comp π) x = σ x
    rw [show ρ.comp π = σ from ZMod.castHom_comp _ _]
  have hcase : σ (g (Fin.last (m + 1))) = 0 ∨ σ (g (Fin.last (m + 1))) = 1 := by
    have hh : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    exact hh _
  rcases hcase with heven | hodd
  · right
    let zero : Fin (m + 2) := (⟨0, by omega⟩ : Fin (m + 1)).castSucc
    let B := g zero
    let v := fun i ↦ g i - B
    have hv : ValidTuple v := validTuple_sub_const g hg B
    have hB : π B = 0 := (hprefix ⟨0, by omega⟩).trans (by norm_num [a])
    have hpref : ∀ i : Fin (m + 1), π (v i.castSucc) = (a i.val : ZMod (2 * L)) := by
      intro i; rw [map_sub, hprefix, hB, sub_zero]
    have hz : v zero = 0 := sub_self B
    have hparity : ρ (π (v (Fin.last (m + 1)))) = 0 := by
      rw [hcomp, map_sub, heven, ← hcomp B, hB, map_zero, sub_zero]
    have hc := scaled_short_prefix_of_even_extra_si_lifts_of_lt_two_pow hm
      (even_two_mul L) hupper v hv hpref hz hparity
    refine ⟨v ((⟨1, by omega⟩ : Fin (m + 1)).castSucc), B, ?_⟩
    intro i
    exact sub_eq_iff_eq_add.mp (hc i)
  · exact Or.inl (exists_valid_si_lift_prefix_of_odd_coset_halving g hg hprefix hodd)

/-- The already proved power-gap rigidity and global bound for coherent
shorter prefixes give fixed-set validity at the actual subbinary modulus. -/
theorem valid_fixed_of_valid_scaled_fixed_short_prefix_lt_two_pow
    {m N : ℕ} [NeZero N] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod N)
    (hprefix : ∀ i : Fin m, g (e i.castSucc.castSucc) = c * (a i.val : ZMod N) + b)
    (hupper : N < 2 ^ (m + 2)) : Valid (m + 2) N := by
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_scaled_fixed_short_prefix_lt_two_pow
    hm g hg e c b hprefix hupper
  have hb := global_lower_bound_of_valid_scaled_fixed_short_prefix hm g hg e c b hprefix
  have hlog := Nat.pow_log_le_self 2 (by omega : m + 2 ≠ 0)
  have hpow := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) ht.le
  have htbound : 2 ^ t ≤ m + 2 := by
    unfold globalBound at hb
    rw [hgap] at hb
    omega
  rw [hgap]
  exact valid_gap (by omega) htbound

end MinModulus
