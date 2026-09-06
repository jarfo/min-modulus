import MinModulus.SIThreeIndexEight

/-!
# Global and exact-stratum bounds for arbitrary three-extra multipliers

Every valid tuple with a coherent prefix c*(2^i-1)+b of length n-3,
for n >= 9, satisfies the full global and every exact-stratum lower bound.
The multiplier c is arbitrary, including nonunits; the three extra entries
are unrestricted. Below 2^n, fixed-set validity holds at the SAME modulus.

Reflected actual-prefix validity and a uniform endpoint ratio bound the
normalized divisor index by eight. All eight index classes are already
closed. Unit-times-divisor normalization then removes the index and unit
restrictions entirely. Direct G1, odd G2, and exceptional G3 consumers
exclude this whole class, without any unrestricted global input. Coherence
in the original modulus remains required: arbitrary independent lifts and
extraction from arbitrary tuples are not proved here.
-/

namespace MinModulus
open Finset

/-- Nine times the fixed prefix endpoint dominates the full three-step
binary range, uniformly from prefix length six onwards. -/
theorem two_pow_add_three_le_nine_mul_globalBound {m : ℕ} (hm : 6 ≤ m) :
    2^(m+3) ≤ 9*globalBound m := by
  have hlin : 9*m ≤ 2^m := by
    induction m, hm using Nat.le_induction with
    | base => norm_num
    | succ m hm ih => rw [pow_succ']; omega
  have hlog := Nat.pow_log_le_self 2 (by omega : m ≠ 0)
  have hpow : 2^(m+3)=8*2^m := by rw [pow_add]; norm_num; ring
  unfold globalBound
  omega

/-- The actual scaled three-extra prefix reflects to fixed validity
downstairs, without an assumed lower bound or any injectivity premise. -/
theorem valid_fixed_of_valid_divisor_fixed_three_extra_prefix
    {m d M : ℕ} (g : Fin (m+3) → ZMod (d*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc=((d*a i.val : ℕ) : ZMod (d*M))) :
    Valid m M := by
  apply valid_fixed_of_valid_divisor_fixed_prefix
    (fun i : Fin (m+1) ↦ g i.castSucc.castSucc)
    (validTuple_embedding ⟨fun i ↦ i.castSucc.castSucc,
      (Fin.castSucc_injective (m+2)).comp (Fin.castSucc_injective (m+1))⟩ g hg)
  exact hpref

/-- Every subbinary coherent three-extra divisor class has index at
most eight. The bound follows from actual reflected prefix validity. -/
theorem divisor_le_eight_of_valid_divisor_fixed_three_extra_prefix_lt_two_pow
    {m d M : ℕ} [NeZero (d*M)] (hm : 6 ≤ m)
    (g : Fin (m+3) → ZMod (d*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc=((d*a i.val : ℕ) : ZMod (d*M)))
    (hupper : d*M < 2^(m+3)) : d ≤ 8 := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne (d*M))
  have hMpos := Nat.pos_of_mul_pos_left hNpos
  letI : NeZero M := ⟨ne_of_gt hMpos⟩
  have hv := valid_fixed_of_valid_divisor_fixed_three_extra_prefix g hg hpref
  have hcard := Fintype.card_le_of_injective _ (validTuple_injective _ (validTuple_fixed_of_valid hv))
  simp only [Fintype.card_fin, ZMod.card] at hcard
  have hbound := (nmin_eq (by omega : 2 ≤ m)).2 ⟨by omega, hv⟩
  change globalBound m ≤ M at hbound
  have hratio := two_pow_add_three_le_nine_mul_globalBound hm
  nlinarith

/-- All divisor indices are consumed. A coherent three-extra prefix
under ANY divisor forces fixed validity at the original subbinary modulus. -/
theorem valid_fixed_of_valid_divisor_fixed_three_extra_prefix_lt_two_pow
    {m d M : ℕ} [NeZero (d*M)] (hm : 6 ≤ m)
    (g : Fin (m+3) → ZMod (d*M)) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc.castSucc.castSucc=((d*a i.val : ℕ) : ZMod (d*M)))
    (hupper : d*M < 2^(m+3)) : Valid (m+3) (d*M) := by
  have hNpos := Nat.pos_of_ne_zero (NeZero.ne (d*M))
  have hdpos := Nat.pos_of_mul_pos_right hNpos
  have hMpos := Nat.pos_of_mul_pos_left hNpos
  letI : NeZero M := ⟨ne_of_gt hMpos⟩
  have hd := divisor_le_eight_of_valid_divisor_fixed_three_extra_prefix_lt_two_pow hm g hg hpref hupper
  have hpre : ∀ i : Fin m, g i.castSucc.castSucc.castSucc=zmodScaleHom d M (a i.val : ZMod M) := by
    simpa only [zmodScaleHom_natCast] using hpref
  interval_cases d
  · simpa using valid_fixed_of_valid_fixed_three_extra_prefix_lt_two_pow
      (by omega) g hg (by simpa using hpref) hupper
  · exact valid_fixed_of_valid_doubled_three_extra_prefix_lt_two_pow (by omega) g hg hpre hupper
  · exact False.elim (not_validTuple_of_tripled_three_extra_prefix_subbinary hm hupper g hpre hg)
  · exact valid_fixed_of_valid_quadrupled_three_extra_prefix_lt_two_pow (by omega) hupper g hg hpre
  · exact False.elim (not_validTuple_of_quintupled_three_extra_prefix_subbinary (by omega) hupper g hpre hg)
  · have h := binary_lower_bound_of_valid_affine_six_or_seven_three_extra_prefix
      (by omega) (by omega : 6 ≤ 6) (by omega : 6 ≤ 7) g hg (Equiv.refl _) (AddEquiv.refl _) 0
      (by simpa using hpre)
    omega
  · have h := binary_lower_bound_of_valid_affine_six_or_seven_three_extra_prefix
      (by omega) (by omega : 6 ≤ 7) (by omega : 7 ≤ 7) g hg (Equiv.refl _) (AddEquiv.refl _) 0
      (by simpa using hpre)
    omega
  · exact valid_fixed_of_valid_octupled_three_extra_prefix_lt_two_pow (by omega) hupper g hg hpre

/-- Arbitrary coherent multipliers, including nonunits, admit the
same-modulus three-extra fixed-validity conclusion in every n>=9. -/
theorem valid_fixed_of_valid_scaled_fixed_three_extra_prefix_lt_two_pow
    {m N : ℕ} [NeZero N] (hm : 6 ≤ m)
    (g : Fin (m+3) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (c b : ZMod N)
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc)=c*(a i.val : ZMod N)+b)
    (hupper : N < 2^(m+3)) : Valid (m+3) N := by
  obtain ⟨d, hd, u, hu, hc⟩ := ZMod.eq_unit_mul_divisor c
  obtain ⟨M, hM⟩ := hd
  subst N
  obtain ⟨v, rfl⟩ := hu
  let φ : ZMod (d*M) ≃+ ZMod (d*M) :=
    (ZMod.AddAutEquivUnits (d*M)).symm (Additive.ofMul v)
  have hv := validTuple_sub_const (fun i ↦ g (e i)) (validTuple_embedding e.toEmbedding g hg) b
  have hw := validTuple_comp hv φ.symm.toAddMonoidHom φ.symm.injective
  apply valid_fixed_of_valid_divisor_fixed_three_extra_prefix_lt_two_pow hm
    (fun i ↦ φ.symm (g (e i)-b)) hw ?_ hupper
  intro i
  apply φ.injective
  rw [φ.apply_symm_apply, hpref, add_sub_cancel_right, hc]
  change (v : ZMod (d*M))*d*(a i.val : ZMod (d*M))=
    (v : ZMod (d*M))*((d*a i.val : ℕ) : ZMod (d*M))
  push_cast
  ring

/-- The full global lower bound for a coherent n-3 SI prefix under ANY
multiplier, with three arbitrary extras, for every n>=9. -/
theorem global_lower_bound_of_valid_scaled_fixed_three_extra_prefix
    {m N : ℕ} [NeZero N] (hm : 6 ≤ m)
    (g : Fin (m+3) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (c b : ZMod N)
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc)=c*(a i.val : ZMod N)+b) :
    globalBound (m+3) ≤ N := by
  by_cases hupper : N < 2^(m+3)
  · have hv := valid_fixed_of_valid_scaled_fixed_three_extra_prefix_lt_two_pow hm g hg e c b hpref hupper
    have hcard := Fintype.card_le_of_injective _ (validTuple_injective g hg)
    simp only [Fintype.card_fin, ZMod.card] at hcard
    exact (nmin_eq (by omega : 2 ≤ m+3)).2 ⟨by omega, hv⟩
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Every exact stratum bound follows for arbitrary coherent three-extra
multipliers, including the odd stratum; no unrestricted gate is assumed. -/
theorem stratum_lower_bound_of_valid_scaled_fixed_three_extra_prefix
    {m N s q : ℕ} [NeZero N] (hm : 6 ≤ m) (hq : Odd q) (hN : N=2^s*q)
    (g : Fin (m+3) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (c b : ZMod N)
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc)=c*(a i.val : ZMod N)+b) :
    stratumBound (m+3) s ≤ N := by
  by_cases hupper : N < 2^(m+3)
  · have hv := valid_fixed_of_valid_scaled_fixed_three_extra_prefix_lt_two_pow hm g hg e c b hpref hupper
    rw [hN] at hv
    simpa only [hN] using stratum_lower_bound_of_valid_fixed (by omega : 3 ≤ m+3) hq hv
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Direct critical-G1 exclusion for the entire arbitrary-multiplier
coherent three-extra class, without a half-witness premise. -/
theorem not_validTuple_of_critical_scaled_fixed_three_extra_prefix
    {m s q : ℕ} (hm : 6 ≤ m) (hq : Odd q)
    (hcritical : 2^s*q < stratumBound (m+3) s)
    (g : Fin (m+3) → ZMod (2^s*q))
    (e : Equiv.Perm (Fin (m+3))) (c b : ZMod (2^s*q))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc)=c*(a i.val : ZMod (2^s*q))+b) :
    ¬ ValidTuple g := by
  intro hg
  have hqpos := hq.pos
  letI : NeZero (2^s*q) := ⟨ne_of_gt (by positivity)⟩
  exact (not_lt_of_ge (stratum_lower_bound_of_valid_scaled_fixed_three_extra_prefix
    hm hq rfl g hg e c b hpref)) hcritical

/-- The full odd G2 threshold holds for all coherent three-extra
multipliers, including odd-modulus nonunits. -/
theorem odd_lower_bound_of_valid_scaled_fixed_three_extra_prefix
    {m N : ℕ} (hm : 6 ≤ m) (hN : Odd N)
    (g : Fin (m+3) → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin (m+3))) (c b : ZMod N)
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc)=c*(a i.val : ZMod N)+b) :
    2^(m+3)-1 ≤ N := by
  letI : NeZero N := ⟨ne_of_gt hN.pos⟩
  simpa [stratumBound] using stratum_lower_bound_of_valid_scaled_fixed_three_extra_prefix
    (s := 0) hm hN (by simp) g hg e c b hpref

/-- Direct G3 exclusion under any coherent three-extra multiplier. -/
theorem not_validTuple_exceptional_of_scaled_fixed_three_extra_prefix
    {m : ℕ} (hm : 6 ≤ m) (hnpow : 2^Nat.log 2 (m+3) ≠ m+3)
    (g : Fin (m+3) → ZMod (2*globalBound (m+2)))
    (e : Equiv.Perm (Fin (m+3))) (c b : ZMod (2*globalBound (m+2)))
    (hpref : ∀ i : Fin m, g (e i.castSucc.castSucc.castSucc)=
      c*(a i.val : ZMod (2*globalBound (m+2)))+b) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (m+2) := (nmin_eq (by omega : 2 ≤ m+2)).1.1
  letI : NeZero (2*globalBound (m+2)) := ⟨by omega⟩
  exact (not_lt_of_ge (global_lower_bound_of_valid_scaled_fixed_three_extra_prefix hm g hg e c b hpref))
    (two_mul_globalBound_lt_succ_of_not_power (by omega) hnpow)

end MinModulus
