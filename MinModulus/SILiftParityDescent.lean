/-
# Parity descent for independently lifted full SI quotient prefixes

For n>=5 and 4 dividing N, a valid tuple below 2^n whose half quotient
contains a unit-affine SI prefix of length n-1 admits a valid (n-1)-tuple
at N/2. Independent lift bits, the remaining entry, and quotient affine
transport are all allowed. No common touch or unrestricted global gate
is assumed. This closes this class of the higher-even G1 deletion input,
not arbitrary G1, the first even stratum, G2, or G3.

A three-term lift defect forces the extra quotient value to be a dyadic
complement. If that extra is even, parity leaves only a forbidden midpoint,
so all interior recurrences hold and the first n-2 actual lifts are
coherent. Power-gap rigidity then constructs a smaller valid fixed tuple.
An odd extra instead gives direct deletion and halving of its parity coset.
The defect localization itself holds for arbitrary positive half moduli
within its displayed cover bound, not just even ones.
-/
import MinModulus.G1ParityFibreDescent
import MinModulus.SIQuarterMinusOne
import MinModulus.SILiftMidpoint

namespace MinModulus
open Finset

/-- An actual three-term lift defect localizes the extra entry to a
dyadic complement. The rival construction omits that extra on both sheets. -/
theorem exists_dyadic_complement_of_valid_si_lift_defect
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : M ≤ 2 * (2 ^ m - 1))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0)
    (j : Fin (m + 1)) (hj : 2 ≤ j.val)
    (hdef : g j.castSucc ≠
      2 • g ((⟨j.val - 1, by omega⟩ : Fin (m + 1)).castSucc) +
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc)) :
    ∃ p : ℕ, (p = 0 ∨ ∃ l ≤ m, p = 2 ^ l) ∧
      ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1))) =
        (1 + (2 ^ j.val : ℕ) : ZMod M) - p := by
  classical
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let u : Fin (m + 1) → ZMod (2 * M) := fun i ↦ g i.castSucc
  let z0 : Fin (m + 1) := ⟨0, by omega⟩
  let z1 : Fin (m + 1) := ⟨1, by omega⟩
  let prev : Fin (m + 1) := ⟨j.val - 1, by omega⟩
  let lo : Multiset (Fin (m + 1)) := Multiset.replicate 2 prev + {z1}
  let hi : Multiset (Fin (m + 1)) := {j} + Multiset.replicate 2 z0
  have ha : 2 * a (j.val - 1) + 1 = a j.val := by
    have hp : 2 ^ j.val = 2 * 2 ^ (j.val - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hpos : 0 < 2 ^ (j.val - 1) := by positivity
    unfold a
    omega
  have hlo : π ((lo.map u).sum) = (a j.val : ZMod M) := by
    simp only [lo, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_singleton, Multiset.sum_singleton,
      map_add, map_nsmul]
    change 2 • π (g prev.castSucc) + π (g z1.castSucc) = _
    dsimp only [π]
    rw [hprefix, hprefix]
    norm_num only [z1, a, pow_one, Nat.reduceSub, Nat.cast_one]
    change 2 • (a (j.val - 1) : ZMod M) + 1 = (a j.val : ZMod M)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      nsmul_eq_mul] using congrArg (fun x : ℕ ↦ (x : ZMod M)) ha
  have hhi : (hi.map u).sum = g j.castSucc := by
    simp only [hi, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
      Multiset.sum_replicate, Multiset.map_singleton, Multiset.sum_singleton]
    change g j.castSucc + 2 • g z0.castSucc = _
    rw [show g z0.castSucc = 0 from hzero, smul_zero, add_zero]
  have hpair : (hi.map u).sum = (lo.map u).sum + M := by
    have hh : π ((hi.map u).sum) = π ((lo.map u).sum) := by
      rw [hhi, hlo]
      exact hprefix j
    rcases eq_or_eq_add_half_of_castHom_eq _ _ hh with heq | heq
    · rw [hhi] at heq
      apply False.elim
      apply hdef
      simpa only [lo, Multiset.map_add, Multiset.sum_add, Multiset.map_replicate,
        Multiset.sum_replicate, Multiset.map_singleton, Multiset.sum_singleton,
        u, prev, z1] using heq
    · exact heq
  let r : ZMod M := π (∑ i, g i) - (a j.val : ZMod M)
  have hholes : r.val + m = 2 ^ (m + 1) ∨
      ∃ l ≤ m, r.val + m + 2 ^ l = 2 ^ (m + 1) := by
    by_contra hnone
    push Not at hnone
    obtain ⟨s, hs, hmem, hsum⟩ := exists_mersenne_coin_multiset_one_fewer hm r.val
      (r.val_lt.trans_le hM) hnone.1 hnone.2
    obtain ⟨v, hv, hvsum⟩ := exists_fixed_multiset_sum_of_nat_coin_representation_card
      (m := m + 1) (N := M) (K := m - 1) (by omega) s hs
      (fun i hi ↦ by have := hmem i hi; omega) hsum
    have hvs : π ((v.map u).sum) = r := by
      rw [map_multiset_sum, Multiset.map_map]
      change (v.map (fun i ↦ π (g i.castSucc))).sum = r
      simpa only [π, hprefix, ZMod.natCast_zmod_val] using hvsum
    obtain ⟨w, hw, hwsum⟩ := exists_multiset_sum_of_antipodal_blocks
      (L := m + 2) u lo hi v (by simp [lo, hi]) hpair
      (by simp only [lo, Multiset.card_add, Multiset.card_replicate,
        Multiset.card_singleton, hv]; omega) (∑ i, g i)
      (by rw [map_add, hvs, hlo]; dsimp only [r]; abel)
    apply not_validTuple_of_multiset_omission g (w.map Fin.castSucc)
      (by simpa only [Multiset.card_map] using hw)
      (by simpa only [Multiset.map_map, Function.comp_def] using hwsum)
      (Fin.last (m + 1)) _ hg
    intro hmem
    obtain ⟨k, _, hk⟩ := Multiset.mem_map.mp hmem
    exact Fin.castSucc_ne_last k hk
  have hsum : r + (a j.val : ZMod M) =
      ((2 ^ (m + 1) - (m + 1) - 1 : ℕ) : ZMod M) + π (g (Fin.last (m + 1))) := by
    dsimp only [r]
    rw [sub_add_cancel, Fin.sum_univ_castSucc, map_add, map_sum]
    congr 1
    dsimp only [π]
    simp only [hprefix]
    rw [← Nat.cast_sum, sum_fixed_eq_cover_hole]
  have hnat : (2 ^ (m + 1) - (m + 1) - 1) + m + 2 = 2 ^ (m + 1) := by
    have := Nat.lt_two_pow_self (n := m + 1)
    omega
  have hcast := congrArg (fun x : ℕ ↦ (x : ZMod M)) hnat
  simp only [Nat.cast_add, Nat.cast_ofNat] at hcast
  have haj : (a j.val : ZMod M) + 1 = ((2 ^ j.val : ℕ) : ZMod M) := by
    have h : a j.val + 1 = 2 ^ j.val := by
      have : 0 < 2 ^ j.val := by positivity
      unfold a; omega
    simpa only [Nat.cast_add, Nat.cast_one] using
      congrArg (fun x : ℕ ↦ (x : ZMod M)) h
  have finish (p : ℕ) (hp : r.val + m + p = 2 ^ (m + 1)) :
      π (g (Fin.last (m + 1))) = (1 + (2 ^ j.val : ℕ) : ZMod M) - p := by
    have hh := congrArg (fun x : ℕ ↦ (x : ZMod M)) hp
    simp only [Nat.cast_add, ZMod.natCast_zmod_val] at hh
    linear_combination hh - hcast - hsum + haj
  rcases hholes with h | ⟨l, hl, h⟩
  · exact ⟨0, Or.inl rfl, finish 0 (by omega)⟩
  · exact ⟨2 ^ l, Or.inr ⟨l, hl, rfl⟩, finish _ h⟩

/-- In an even quotient, an even dyadic complement of a positive power
can only be that power itself. -/
theorem eq_two_pow_of_even_dyadic_complement
    {M j p : ℕ} (hM : Even M) (hj : 1 ≤ j)
    (hp : p = 0 ∨ ∃ l, p = 2 ^ l) (x : ZMod M)
    (hx : ZMod.castHom hM.two_dvd (ZMod 2) x = 0)
    (heq : x = (1 + (2 ^ j : ℕ) : ZMod M) - p) :
    x = ((2 ^ j : ℕ) : ZMod M) := by
  have hpow (k : ℕ) (hk : 1 ≤ k) : ((2 ^ k : ℕ) : ZMod 2) = 0 := by
    simp only [Nat.cast_pow, Nat.cast_ofNat, show (2 : ZMod 2) = 0 by decide,
      zero_pow (by omega : k ≠ 0)]
  have hpar := congrArg (ZMod.castHom hM.two_dvd (ZMod 2)) heq
  rw [hx, map_sub, map_add, map_one, map_natCast, map_natCast, hpow j hj] at hpar
  rcases hp with rfl | ⟨l, rfl⟩
  · norm_num at hpar
  · by_cases hl : l = 0
    · simpa [hl] using heq
    · rw [hpow l (by omega)] at hpar
      norm_num at hpar

/-- Below the binary threshold, an even extra in an even half quotient
rules out every interior three-term defect of the full SI prefix. -/
theorem si_lift_recurrence_of_even_extra_of_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : Even M)
    (hupper : 2 * M < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0)
    (heven : ZMod.castHom hM.two_dvd (ZMod 2)
      (ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1)))) = 0)
    (j : Fin m) (hj : 2 ≤ j.val) :
    g j.castSucc.castSucc =
      2 • g ((⟨j.val - 1, by omega⟩ : Fin (m + 1)).castSucc) +
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) := by
  by_contra hdef
  have hsize : M ≤ 2 * (2 ^ m - 1) := by
    have hp : 2 ^ (m + 2) = 4 * 2 ^ m := by rw [pow_add]; norm_num; ring
    obtain ⟨r, hr⟩ := hM
    have hpos : 0 < 2 ^ m := by positivity
    omega
  obtain ⟨p, hp, hx⟩ := exists_dyadic_complement_of_valid_si_lift_defect
    hm hsize g hg hprefix hzero j.castSucc hj hdef
  have hxpow := eq_two_pow_of_even_dyadic_complement hM (by omega : 1 ≤ j.val)
    (p := p) (hp.imp_right (fun ⟨l, _, hl⟩ ↦ ⟨l, hl⟩)) _ heven hx
  let next : Fin (m + 1) := ⟨j.val + 1, by omega⟩
  let one : Fin (m + 1) := ⟨1, by omega⟩
  have hne : next ≠ one := by intro h; have := congrArg Fin.val h; dsimp [next, one] at this; omega
  have hmid : 2 • ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (Fin.last (m + 1))) = (a next.val : ZMod M) + (a one.val : ZMod M) := by
    rw [hxpow]
    have hn : 2 * 2 ^ j.val = a (j.val + 1) + a 1 := by
      have : 0 < 2 ^ j.val := by positivity
      unfold a
      rw [pow_succ']
      norm_num
      omega
    simpa only [next, one, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
      nsmul_eq_mul] using congrArg (fun k : ℕ ↦ (k : ZMod M)) hn
  have hb := two_pow_le_of_valid_si_lift_prefix_midpoint hm g hg hprefix next one hne hmid
  omega

/-- An even extra forces the first n-2 actual lifts to be coherent below
the binary threshold. The multiplier is the actual lifted one. -/
theorem scaled_short_prefix_of_even_extra_si_lifts_of_lt_two_pow
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : Even M)
    (hupper : 2 * M < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M))
    (hzero : g ((⟨0, by omega⟩ : Fin (m + 1)).castSucc) = 0)
    (heven : ZMod.castHom hM.two_dvd (ZMod 2)
      (ZMod.castHom (dvd_mul_left M 2) (ZMod M) (g (Fin.last (m + 1)))) = 0) :
    ∀ i : Fin m, g i.castSucc.castSucc =
      g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) * (a i.val : ZMod (2 * M)) := by
  have aux : ∀ k (hk : k < m),
      g ((⟨k, by omega⟩ : Fin (m + 1)).castSucc) =
        g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) * (a k : ZMod (2 * M)) := by
    intro k
    induction k with
    | zero => intro hk; simpa [a] using hzero
    | succ k ih =>
      intro hk
      by_cases hk0 : k = 0
      · subst k; simp [a]
      · have hr := si_lift_recurrence_of_even_extra_of_lt_two_pow hm hM hupper
          g hg hprefix hzero heven (⟨k + 1, hk⟩ : Fin m) (by change 2 ≤ k + 1; omega)
        change g ((⟨k + 1, by omega⟩ : Fin (m + 1)).castSucc) =
          2 • g ((⟨k, by omega⟩ : Fin (m + 1)).castSucc) +
            g ((⟨1, by omega⟩ : Fin (m + 1)).castSucc) at hr
        rw [hr, ih (by omega)]
        have ha : a (k + 1) = 2 * a k + 1 := by
          have : 0 < 2 ^ k := by positivity
          unfold a; rw [pow_succ']; omega
        rw [ha]
        simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one, nsmul_eq_mul]
        ring
  intro i
  exact aux i.val i.isLt

/-- A subbinary valid full SI lift prefix over an even half modulus either
already descends through a parity coset or has a coherent n-2 prefix.
This derives structure from the actual lift bits, rather than assuming it. -/
theorem half_descent_or_scaled_short_prefix_of_even_si_lifts
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : Even M)
    (hupper : 2 * M < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M)) :
    AdmitsValidTuple (m + 1) M ∨
      ∃ c b : ZMod (2 * M), ∀ i : Fin m,
        g i.castSucc.castSucc = c * (a i.val : ZMod (2 * M)) + b := by
  classical
  let π := ZMod.castHom (dvd_mul_left M 2) (ZMod M)
  let ρ := ZMod.castHom hM.two_dvd (ZMod 2)
  let σ := ZMod.castHom (dvd_mul_right 2 M) (ZMod 2)
  have hcomp (x : ZMod (2 * M)) : ρ (π x) = σ x := by
    change (ρ.comp π) x = σ x
    rw [show ρ.comp π = σ from ZMod.castHom_comp _ _]
  let z : Fin (m + 2) := (⟨0, by omega⟩ : Fin (m + 1)).castSucc
  let B := g z
  let v := fun i ↦ g i - B
  have hv : ValidTuple v := validTuple_sub_const g hg B
  have hB : π B = 0 := (hprefix ⟨0, by omega⟩).trans (by norm_num [a])
  have hpref : ∀ i : Fin (m + 1), π (v i.castSucc) = (a i.val : ZMod M) := by
    intro i
    rw [map_sub, hprefix, hB, sub_zero]
  have hz : v z = 0 := sub_self B
  have hcase : ρ (π (v (Fin.last (m + 1)))) = 0 ∨
      ρ (π (v (Fin.last (m + 1)))) = 1 := by
    have h : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
    exact h _
  rcases hcase with heven | hodd
  · right
    have hc := scaled_short_prefix_of_even_extra_si_lifts_of_lt_two_pow
      hm hM hupper v hv hpref hz heven
    refine ⟨v ((⟨1, by omega⟩ : Fin (m + 1)).castSucc), B, ?_⟩
    intro i
    exact sub_eq_iff_eq_add.mp (hc i)
  · left
    apply admitsValidTuple_half_of_all_but_one_same_parity v hv z 1
    intro i
    refine Fin.lastCases ?_ (fun k ↦ ?_) i
    · intro _
      exact (hcomp _).symm.trans hodd
    · intro hk
      rw [← hcomp, hpref, map_natCast]
      have hkpos : 1 ≤ k.val := by
        by_contra h
        apply hk
        apply Fin.ext
        change k.val = 0
        omega
      have ha : a k.val + 1 = 2 ^ k.val := by
        have : 0 < 2 ^ k.val := by positivity
        unfold a; omega
      have hh := congrArg (fun x : ℕ ↦ (x : ZMod 2)) ha
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat,
        show (2 : ZMod 2) = 0 by decide, zero_pow (by omega : k.val ≠ 0)] at hh
      have h2 : (1 : ZMod 2) + 1 = 0 := by decide
      linear_combination hh - h2

/-- Power-gap rigidity gives a valid smaller fixed tuple at half of every
subbinary even modulus carrying a coherent n-2 SI prefix. Any multiplier
is allowed, and the smaller tuple need not be a canonical deleted quotient. -/
theorem admitsValidTuple_half_of_subbinary_scaled_fixed_short_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m)
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (c b : ZMod (2 * M))
    (hprefix : ∀ i : Fin m,
      g (e i.castSucc.castSucc) = c * (a i.val : ZMod (2 * M)) + b)
    (hupper : 2 * M < 2 ^ (m + 2)) : AdmitsValidTuple (m + 1) M := by
  have hpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  obtain ⟨t, ht, hgap⟩ := exists_power_gap_of_valid_scaled_fixed_short_prefix_lt_two_pow
    hm g hg e c b hprefix hupper
  have hbound := global_lower_bound_of_valid_scaled_fixed_short_prefix hm g hg e c b hprefix
  have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) ht.le
  have hlog := Nat.pow_log_le_self 2 (by omega : m + 2 ≠ 0)
  have htle : 2 ^ t ≤ m + 2 := by
    rw [hgap] at hbound
    unfold globalBound at hbound
    omega
  have hpow : 2 ^ (m + 2) = 2 * 2 ^ (m + 1) := by rw [pow_succ']
  have htpos : 1 ≤ t := by
    by_contra h
    have ht0 : t = 0 := by omega
    rw [ht0, pow_zero] at hgap
    omega
  have htpow : 2 ^ t = 2 * 2 ^ (t - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hhalf : M = 2 ^ (m + 1) - 2 ^ (t - 1) := by omega
  have hv : Valid (m + 1) M := by
    rw [hhalf]
    exact valid_gap (by omega) (by omega : 2 ^ (t - 1) ≤ m + 1)
  exact ⟨_, validTuple_fixed_of_valid hv⟩

/-- Actual half-modulus descent for a full independently lifted SI quotient
prefix throughout the subbinary range, whenever the half modulus is even.
Odd extras descend through their parity coset; even extras force a coherent
shorter prefix, whose power gap constructs the smaller fixed tuple. -/
theorem admitsValidTuple_half_of_subbinary_even_si_lift_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : Even M)
    (hupper : 2 * M < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g i.castSucc) = (a i.val : ZMod M)) :
    AdmitsValidTuple (m + 1) M := by
  rcases half_descent_or_scaled_short_prefix_of_even_si_lifts hm hM hupper g hg hprefix with
    hdone | ⟨c, b, hp⟩
  · exact hdone
  · exact admitsValidTuple_half_of_subbinary_scaled_fixed_short_prefix
      hm g hg (Equiv.refl _) c b hp hupper

/-- Quotient affine transport and arbitrary reindexing preserve the
higher-even-stratum deletion theorem throughout the subbinary range.
Upstairs lift bits remain arbitrary. -/
theorem admitsValidTuple_half_of_subbinary_even_quotient_affine_si_prefix
    {m M : ℕ} [NeZero M] (hm : 3 ≤ m) (hM : Even M)
    (hupper : 2 * M < 2 ^ (m + 2))
    (g : Fin (m + 2) → ZMod (2 * M)) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m + 2))) (φ : ZMod M ≃+ ZMod M) (b : ZMod M)
    (hprefix : ∀ i : Fin (m + 1), ZMod.castHom (dvd_mul_left M 2) (ZMod M)
      (g (e i.castSucc)) = φ (a i.val) + b) :
    AdmitsValidTuple (m + 1) M := by
  have hpos := Nat.pos_of_ne_zero (NeZero.ne M)
  letI : NeZero (2 * M) := ⟨by omega⟩
  obtain ⟨Φ, hΦ⟩ := exists_addEquiv_lift_castHom (dvd_mul_left M 2) φ
  let B : ZMod (2 * M) := b.val
  let w := fun i ↦ Φ.symm (g (e i) - B)
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) B
  have hw : ValidTuple w := validTuple_comp hv Φ.symm.toAddMonoidHom Φ.symm.injective
  apply admitsValidTuple_half_of_subbinary_even_si_lift_prefix hm hM hupper w hw
  intro i
  apply φ.injective
  rw [← hΦ, Φ.apply_symm_apply, map_sub, hprefix]
  simp [B]

end MinModulus
