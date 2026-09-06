/-
# First-even constraints from independent SI lift defects

For n = m+2 >= 5, an odd half modulus M in the first-even critical range
2*M < 2^n-2, and a full SI quotient prefix of length n-1, validity forces
exactly one defect among the first n-2 actual lifts relative to the tuple's
own lifted-one multiplier. Quotient affine transport is included.

The one-fewer-coin localization gives one positive even dyadic complement
per interior defect. Two defects would give equal even sums of two powers
of two below 2*M. Oddness removes modular wraparound; binary uniqueness
then forces a forbidden quotient collision. No finite census or open global
gate is an input. The single-defect case, terminal prefix lift, and extra
remain unresolved; this does not prove unrestricted G1 or global_lower_bound.
-/
import MinModulus.SILiftParityDescent
import MinModulus.SIHalfDeletionStrata

namespace MinModulus
open Finset

/-- Below two odd periods, equal even residues cannot differ by one period. -/
theorem eq_of_even_natCast_eq_of_lt_two_mul_odd
    {M A B : ℕ} (hM : Odd M) (hA : Even A) (hB : Even B)
    (hAl : A < 2 * M) (hBl : B < 2 * M)
    (heq : (A : ZMod M) = (B : ZMod M)) : A = B := by
  have hmod : A % M = B % M := by
    have hh := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast] using hh
  have hqa : A / M < 2 := (Nat.div_lt_iff_lt_mul hM.pos).mpr (by omega)
  have hqb : B / M < 2 := (Nat.div_lt_iff_lt_mul hM.pos).mpr (by omega)
  have ha01 : A / M = 0 ∨ A / M = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hqa)
  have hb01 : B / M = 0 ∨ B / M = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ hqb)
  have ha := Nat.mod_add_div A M
  have hb := Nat.mod_add_div B M
  obtain ⟨a, ha2⟩ := hA
  obtain ⟨b, hb2⟩ := hB
  obtain ⟨c, hc2⟩ := hM
  rcases ha01 with h | h <;> rw [h] at ha <;>
    rcases hb01 with hh | hh <;> rw [hh] at hb <;>
    simp only [mul_zero, mul_one, add_zero] at ha hb <;> omega

/-- Two binary-power sums with distinct specified summands have only the
crossed equality. No modulus or tuple hypothesis is needed. -/
theorem two_pow_cross_eq_of_add_eq_of_lt
    {j k u v : ℕ} (hjk : j < k)
    (h : 2 ^ j + 2 ^ v = 2 ^ k + 2 ^ u) :
    2 ^ u = 2 ^ j ∧ 2 ^ v = 2 ^ k := by
  have hjkpow := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) hjk
  have hpos (l : ℕ) : 0 < 2 ^ l := by positivity
  have hstep (l : ℕ) (hl : 1 ≤ l) : 2 ^ l = 2 * 2 ^ (l - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hvk : v = k := by
    rcases lt_trichotomy v k with hv | hv | hv
    · have hpv := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : v ≤ k - 1)
      have hpj := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : j ≤ k - 1)
      have hs := hstep k (by omega)
      have hu := hpos u
      omega
    · exact hv
    · by_cases huv : u < v
      · have hpu := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : u ≤ v - 1)
        have hpk := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : k ≤ v - 1)
        have hs := hstep v (by omega)
        have hj := hpos j
        omega
      · have hpu := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : v ≤ u)
        omega
  rw [hvk] at h ⊢
  exact ⟨by omega, rfl⟩

/-- The two smallest dyadic-complement exceptions are quotient midpoints
and cannot occur in any subbinary full-prefix lift extension. -/
theorem not_validTuple_of_subbinary_si_lift_extra_near_power
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (hupper : 2 * M < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (j : Fin m) (hj : 2 ≤ j.val)
    (hx : ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
        ((2 ^ j.val : ℕ) : ZMod M) ∨
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
        1 + ((2 ^ j.val : ℕ) : ZMod M)) : ¬ ValidTuple g := by
  intro hg
  let next : Fin (m + 1) := ⟨j.val + 1, by omega⟩
  have ha : (a next.val : ZMod M) + 1 = 2 * ((2 ^ j.val : ℕ) : ZMod M) := by
    have hh : a (j.val + 1) + 1 = 2 * 2 ^ j.val := by
      have : 0 < 2 ^ j.val := by positivity
      unfold a; rw [pow_succ']; omega
    simpa only [next, Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun k : ℕ ↦ (k : ZMod M)) hh
  dsimp only [a] at ha
  have hbound : 2 ^ (m + 2) ≤ 2 * M := by
    rcases hx with hx | hx
    · apply two_pow_le_of_valid_si_lift_prefix_midpoint hm g hg hprefix next
        (⟨1, by omega⟩ : Fin (m + 1))
        (by intro h; have := congrArg Fin.val h; dsimp [next] at this; omega)
      rw [hx, two_nsmul]
      norm_num only [a, pow_one, Nat.reduceSub, Nat.cast_one]
      linear_combination -ha
    · apply two_pow_le_of_valid_si_lift_prefix_midpoint hm g hg hprefix next
        (⟨2, by omega⟩ : Fin (m + 1))
        (by intro h; have := congrArg Fin.val h; dsimp [next] at this; omega)
      rw [hx, two_nsmul]
      norm_num only [a, Nat.reducePow, Nat.reduceSub, Nat.cast_ofNat]
      linear_combination -ha
  omega

/-- A valid subbinary interior defect leaves only positive even dyadic
complements. This holds before imposing an odd half modulus. -/
theorem exists_positive_dyadic_complement_of_valid_si_lift_defect
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0)
    (j : Fin m) (hj : 2 ≤ j.val)
    (hdef : g j.castSucc.castSucc ≠
      2 • g ((⟨j.val - 1, by omega⟩ : Fin (m + 1)).castSucc) +
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc)) :
    ∃ l, 1 ≤ l ∧ l ≤ m ∧
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
        (1 + (2 ^ j.val : ℕ) : ZMod M) - (2 ^ l : ℕ) := by
  have hupper : 2 * M < 2 ^ (m + 2) := by
    have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; norm_num; ring
    have hpos : 0 < 2 ^ m := by positivity
    omega
  obtain ⟨p, hp, hx⟩ := exists_dyadic_complement_of_valid_si_lift_defect
    hm hM g hg hprefix hzero j.castSucc hj hdef
  change ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
    (1 + (2 ^ j.val : ℕ) : ZMod M) - p at hx
  rcases hp with rfl | ⟨l, hl, rfl⟩
  · exact False.elim (not_validTuple_of_subbinary_si_lift_extra_near_power hm hupper g hprefix
      j hj (Or.inr (by simpa only [Nat.cast_zero, sub_zero] using hx)) hg)
  · by_cases hl0 : l = 0
    · exact False.elim (not_validTuple_of_subbinary_si_lift_extra_near_power hm hupper g hprefix
        j hj (Or.inl (by simpa [hl0] using hx)) hg)
    · exact ⟨l, by omega, hl, hx⟩

/-- At an odd half modulus, two interior lift defects have compatible
dyadic complements only at the quotient value one. The odd period and
the universal binary subgroup bound prevent modular wraparound. -/
theorem extra_eq_one_of_valid_odd_si_lifts_two_interior_defects
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0)
    (j k : Fin m) (hj : 2 ≤ j.val) (hk : 2 ≤ k.val) (hjk : j ≠ k)
    (hjdef : g j.castSucc.castSucc ≠
      2 • g ((⟨j.val - 1, by omega⟩ : Fin (m + 1)).castSucc) +
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc))
    (hkdef : g k.castSucc.castSucc ≠
      2 • g ((⟨k.val - 1, by omega⟩ : Fin (m + 1)).castSucc) +
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc)) :
    ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) = 1 := by
  obtain ⟨u, hu1, hum, hxu⟩ := exists_positive_dyadic_complement_of_valid_si_lift_defect
    hm hM g hg hprefix hzero j hj hjdef
  obtain ⟨v, hv1, hvm, hxv⟩ := exists_positive_dyadic_complement_of_valid_si_lift_defect
    hm hM g hg hprefix hzero k hk hkdef
  have hbinary := two_pow_pred_le_card_of_validTuple g hg
  simp only [ZMod.card, show m + 2 - 1 = m + 1 by omega, pow_succ'] at hbinary
  have hfloor : 2 ^ m ≤ M := by omega
  have hcast : ((2 ^ j.val + 2 ^ v : ℕ) : ZMod M) =
      ((2 ^ k.val + 2 ^ u : ℕ) : ZMod M) := by
    simp only [Nat.cast_add]
    linear_combination hxv - hxu
  have hpar (l : ℕ) (hl : 1 ≤ l) : Even (2 ^ l) := by
    apply even_iff_two_dvd.mpr
    simpa only [pow_one] using Nat.pow_dvd_pow 2 hl
  have hjbound := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) j.isLt
  have hkbound := Nat.pow_lt_pow_right (by decide : 1 < (2 : ℕ)) k.isLt
  have hubound := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hum
  have hvbound := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hvm
  have heq := eq_of_even_natCast_eq_of_lt_two_mul_odd hq
    ((hpar j.val (by omega)).add (hpar v hv1))
    ((hpar k.val (by omega)).add (hpar u hu1)) (by omega) (by omega) hcast
  have hp : 2 ^ u = 2 ^ j.val := by
    have hne : j.val ≠ k.val := fun h ↦ hjk (Fin.ext h)
    rcases lt_or_gt_of_ne hne with hjk | hkj
    · exact (two_pow_cross_eq_of_add_eq_of_lt hjk heq).1
    · exact (two_pow_cross_eq_of_add_eq_of_lt hkj heq.symm).2
  rw [hp] at hxu
  simpa only [add_sub_cancel_right] using hxu

/-- Two interior defects are impossible in the first-even critical full-
prefix class: the forced quotient collision contradicts the already proved
actual short-prefix collision bound. No unrestricted global gate is used. -/
theorem not_validTuple_of_odd_si_lifts_two_interior_defects
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0)
    (j k : Fin m) (hj : 2 ≤ j.val) (hk : 2 ≤ k.val) (hjk : j ≠ k)
    (hjdef : g j.castSucc.castSucc ≠
      2 • g ((⟨j.val - 1, by omega⟩ : Fin (m + 1)).castSucc) +
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc))
    (hkdef : g k.castSucc.castSucc ≠
      2 • g ((⟨k.val - 1, by omega⟩ : Fin (m + 1)).castSucc) +
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc)) : ¬ ValidTuple g := by
  intro hg
  have hx := extra_eq_one_of_valid_odd_si_lifts_two_interior_defects
    hm hq hM g hg hprefix hzero j k hj hk hjk hjdef hkdef
  have hlog : 1 ≤ Nat.log 2 (m + 2) :=
    (Nat.le_log_iff_pow_le (by decide) (by omega : m + 2 ≠ 0)).mpr (by norm_num)
  have hcritical : 2 * M < stratumBound (m + 2) 1 := by
    unfold stratumBound
    rw [min_eq_left hlog]
    norm_num only [pow_one]
    have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; norm_num; ring
    have hpos : 0 < 2 ^ m := by positivity
    omega
  apply not_validTuple_of_critical_tail_collision_quotient_scaled_short_prefix
    hm hq (by simp) hcritical g (Equiv.refl _) 1 0 (Fin.last (m + 1))
    (by simp) ((⟨1, by omega⟩ : Fin (m + 1)).castSucc)
    (Fin.castSucc_ne_last _) _ _ hg
  · simp only [Equiv.refl_apply]
    rw [hx, hprefix]
    norm_num [a]
  · intro i
    simp only [one_mul, add_zero, Equiv.refl_apply]
    exact hprefix i.castSucc

/-- Doubling erases lift bits, so the interior recurrence right-hand side
always equals the SI entry scaled by the actual lifted one. -/
theorem si_lift_recurrence_rhs_eq_scaled_entry
    {m M : ℕ} [NeZero M] (hm : 2 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M))
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (j : Fin m) (hj : 1 ≤ j.val) :
    2 • g ((⟨j.val - 1, by omega⟩ : Fin (m + 1)).castSucc) +
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) =
      g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) * (a j.val : ZMod (2 * M)) := by
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let c := g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc)
  let prev : Fin (m + 1) := ⟨j.val - 1, by omega⟩
  have hc : π c = 1 := (hprefix ⟨1, by omega⟩).trans (by norm_num [a])
  have heq : π (g prev.castSucc) = π (c * (a (j.val - 1) : ZMod (2 * M))) := by
    rw [map_mul, map_natCast, hc, one_mul]
    exact hprefix prev
  have htwo := nsmul_eq_of_even_of_castHom_eq (by decide : Even 2) _ _ heq
  have ha : a j.val = 2 * a (j.val - 1) + 1 := by
    have hp : 2 ^ j.val = 2 * 2 ^ (j.val - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hpos : 0 < 2 ^ (j.val - 1) := by positivity
    unfold a; omega
  change 2 • g prev.castSucc + c = c * (a j.val : ZMod (2 * M))
  rw [htwo, ha]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, nsmul_eq_mul]
  ring

/-- A hypothetical critical first-even full-prefix lift has exactly ONE
noncoherent entry among its first n-2 coordinates. Zero defects violate
the coherent class bound; two violate the odd-period dyadic intersection.
The terminal prefix lift and the extra remain unrestricted here. -/
theorem exists_unique_short_prefix_defect_of_critical_odd_si_lifts
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0) :
    ∃! j : Fin m, g j.castSucc.castSucc ≠
      g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) * (a j.val : ZMod (2 * M)) := by
  classical
  let c := g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc)
  have hbase (i : Fin m) (hi : i.val ≤ 1) :
      g i.castSucc.castSucc = c * (a i.val : ZMod (2 * M)) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with hi | hi
    · have he : i.castSucc.castSucc = ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) := by
        apply Fin.ext; simpa only [Fin.val_castSucc] using hi
      rw [he, hzero, hi]
      norm_num [a]
    · have he : i.castSucc.castSucc = ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) := by
        apply Fin.ext; simpa only [Fin.val_castSucc] using hi
      rw [he, hi]
      norm_num [a, c]
  have hcrit : 2 * M < stratumBound (m + 2) 1 := by
    have hlog : 1 ≤ Nat.log 2 (m + 2) :=
      (Nat.le_log_iff_pow_le (by decide) (by omega : m + 2 ≠ 0)).mpr (by norm_num)
    unfold stratumBound
    rw [min_eq_left hlog]
    norm_num only [pow_one]
    have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; norm_num; ring
    have hpos : 0 < 2 ^ m := by positivity
    omega
  have hex : ∃ j : Fin m, g j.castSucc.castSucc ≠ c * (a j.val : ZMod (2 * M)) := by
    by_contra hnone
    push Not at hnone
    apply not_validTuple_of_critical_scaled_fixed_short_prefix (m := m) (s := 1) (q := M)
      hm hq hcrit g
      (Equiv.refl _) c 0 _ hg
    intro i
    simpa only [Equiv.refl_apply, add_zero] using hnone i
  obtain ⟨j, hjdef⟩ := hex
  have hj : 2 ≤ j.val := by
    by_contra h; exact hjdef (hbase j (by omega))
  refine ⟨j, hjdef, ?_⟩
  intro k hkdef
  by_contra hkj
  have hk : 2 ≤ k.val := by
    by_contra h; exact hkdef (hbase k (by omega))
  apply not_validTuple_of_odd_si_lifts_two_interior_defects hm hq hM g hprefix hzero
    j k hj hk (fun h ↦ hkj h.symm) _ _ hg
  · rw [si_lift_recurrence_rhs_eq_scaled_entry (by omega) g hprefix j (by omega)]
    exact hjdef
  · rw [si_lift_recurrence_rhs_eq_scaled_entry (by omega) g hprefix k (by omega)]
    exact hkdef

/-- Quotient affine transport yields a unique actual shorter-prefix defect
with respect to the original tuple's own lifted-one difference and zero.
No coherence or choice of independent lift bits is assumed. -/
theorem exists_unique_short_prefix_defect_of_critical_odd_quotient_affine_si_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hq : Odd M)
    (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b) :
    ∃! j : Fin m, g (e j.castSucc.castSucc) ≠
      (g (e ((⟨1, by omega⟩ : Fin (m + 1)).castSucc)) -
        g (e ((⟨0, by omega⟩ : Fin (m + 1)).castSucc))) * (a j.val : ZMod (2 * M)) +
          g (e ((⟨0, by omega⟩ : Fin (m + 1)).castSucc)) := by
  have hpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left M 2) φ
  let zero : Fin (m + 2) := (⟨0, by omega⟩ : Fin (m + 1)).castSucc
  let one : Fin (m + 2) := (⟨1, by omega⟩ : Fin (m + 1)).castSucc
  let B := g (e zero)
  let C := g (e one) - B
  let w := fun i ↦ Φ.symm (g (e i) - B)
  have hB : ZMod.castHom (dvd_mul_left M 2) (ZMod M) B = b := by
    simpa only [a, pow_zero, Nat.sub_self, Nat.cast_zero, map_zero, zero_add] using hprefix ⟨0, by omega⟩
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) B
  have hw : ValidTuple w := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  have hpref : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (w i.castSucc) = (a i.val : ZMod M) := by
    intro i
    apply φ.injective
    rw [← hΦ, Φ.apply_symm_apply, map_sub, hprefix, hB, add_sub_cancel_right]
  have hz : w zero = 0 := by simp [w, B]
  obtain ⟨j, hj, huniq⟩ := exists_unique_short_prefix_defect_of_critical_odd_si_lifts
    hm hq hM w hw hpref hz
  have hmul (i : Fin m) : Φ (w one * (a i.val : ZMod (2 * M))) =
      C * (a i.val : ZMod (2 * M)) := by
    calc
      _ = Φ ((a i.val) • w one) := by
        congr 1; simp only [nsmul_eq_mul]; ring
      _ = (a i.val) • Φ (w one) := map_nsmul Φ _ _
      _ = _ := by
        simp only [w, Φ.apply_symm_apply, C, nsmul_eq_mul]
        ring
  have heq (i : Fin m) :
      w i.castSucc.castSucc = w one * (a i.val : ZMod (2 * M)) ↔
        g (e i.castSucc.castSucc) = C * (a i.val : ZMod (2 * M)) + B := by
    constructor
    · intro h
      have hh := congrArg Φ h
      rw [hmul, show Φ (w i.castSucc.castSucc) = g (e i.castSucc.castSucc) - B from
        Φ.apply_symm_apply _] at hh
      exact sub_eq_iff_eq_add.mp hh
    · intro h
      apply Φ.injective
      rw [hmul, show Φ (w i.castSucc.castSucc) = g (e i.castSucc.castSucc) - B from
        Φ.apply_symm_apply _]
      exact sub_eq_iff_eq_add.mpr h
  refine ⟨j, (not_congr (heq j)).mp hj, ?_⟩
  intro k hk
  exact huniq k ((not_congr (heq k)).mpr hk)

end MinModulus
