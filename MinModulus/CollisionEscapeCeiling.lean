import MinModulus.CollisionEscapeThreshold

/-! Round the collision-inclusive average arm length upward. The
stronger scalar condition retains every original exact-stratum and
global conclusion, and the all-shift G3 restriction includes actual
opposite pairs. All unrestricted global gates remain open. -/

namespace MinModulus
open Finset

/-- The rounded-up average retains the cycle and interval thresholds. -/
theorem escape_ceiling_conditions_of_binomial_charge
    {n r : ℕ} (hn : 4 ≤ n) (hr : 0 < r)
    (hc : (n+r-1).choose r ≤ 2^((n+r-1)/r-3)) :
    6*r ≤ n ∧ 4 ≤ (n+r-1)/r ∧ 2*n+1 ≤ 2^((n+r-1)/r) := by
  have hchoose : n ≤ (n+r-1).choose r := by
    simpa only [Nat.add_sub_cancel,Nat.choose_one_right] using
      forest_binomial_mono_rank (by omega : 0 < n) (by omega : 1 ≤ r)
  have hsize := hchoose.trans hc
  let c := (n+r-1)/r
  change n ≤ 2^(c-3) at hsize
  have hcn : c ≤ n := by
    apply Nat.div_le_of_le_mul
    have hn1 : n-1+1=n := by omega
    have hprod : r*(n-1)+r=r*n := by
      calc
        _=r*((n-1)+1) := by ring
        _=r*n := by rw [hn1]
    have hmul := Nat.mul_le_mul_right (n-1) (by omega : 1 ≤ r)
    simp only [one_mul] at hmul
    omega
  have hlarge : 6 ≤ c := by
    by_contra hh
    have hp : 2^(c-3) ≤ 4 := by
      have he := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : c-3 ≤ 2)
      norm_num at he
      exact he
    have hp' : 2^(c-3) ≤ 2 := by
      have he := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : c-3 ≤ 1)
      norm_num at he
      exact he
    omega
  have hmul : c*r ≤ n+r-1 := Nat.div_mul_le_self _ _
  have hwide : 6*r ≤ n := by
    by_contra hh
    have hc6 : c ≤ 6 := by
      by_contra hz
      have he := Nat.mul_le_mul_right r (by omega : 7 ≤ c)
      omega
    have hce : c=6 := by omega
    have hp : 2^(c-3)=8 := by rw [hce]; norm_num
    change n ≤ 2^(c-3) at hsize
    rw [hp] at hsize
    rw [hce] at hmul
    have hr1 : r=1 := by omega
    have hcn' : c=n := by simp [c,hr1]
    omega
  have hpow : 2^c=8*2^(c-3) := by
    rw [show c=3+(c-3) by omega,pow_add]
    norm_num
  exact ⟨hwide,by omega,by change 2*n+1 ≤ 2^c; change n ≤ 2^(c-3) at hsize; omega⟩

/-- A single collision costs at most one arm in the scalar packing
threshold. No doubling injectivity is assumed about the actual tuple. -/
theorem binary_card_bound_of_acyclic_escape_ceiling_threshold_with_one_collision
    {n r : ℕ} (hn : 4 ≤ n) {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (A : Finset (Fin n)) (hcard : A.card=r) (b : G)
    (hA : ∀ i, i ∈ A ↔ ¬ ∃ l, g l=2 • g i+b)
    (hacyclic : ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin n, ∀ P : Equiv.Perm (Fin m),
      ¬ (∀ i, g (e (P i))=2 • g (e i)+b))
    (hcharge : (n+r).choose (r+1) ≤ 2^((n+r)/(r+1)-3)) : 2^n ≤ Fintype.card G := by
  classical
  obtain ⟨_,havg,hwide⟩ := escape_ceiling_conditions_of_binomial_charge hn (by omega : 0 < r+1)
    (by simpa only [show n+(r+1)-1=n+r by omega] using hcharge)
  simp only [show n+(r+1)-1=n+r by omega] at havg hwide
  obtain ⟨B,_,hB,L,hL,E,x,hchain,a,hmax,hgen⟩ :=
    exists_affine_forest_with_longest_genuine_arm_of_one_collision (by omega) g hg hh hinv A b hA hacyclic
  have hsize : (∑ c, L c)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hnL : n ≤ (r+1)*L a := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦ hmax c)
    simp only [hsize,Finset.sum_const,Finset.card_univ,Fintype.card_coe,smul_eq_mul] at hs
    exact hs.trans (Nat.mul_le_mul_right (L a) (by omega))
  have hLa : (n+r)/(r+1) ≤ L a := by
    apply Nat.le_of_lt_succ
    apply (Nat.div_lt_iff_lt_mul (by omega : 0 < r+1)).mpr
    nlinarith
  apply binary_card_bound_of_one_genuine_arm_short_interval (by omega) L hL g hg E x b hchain a
    (hwide.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hLa)) (by omega) ?_
    (hgen ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega))
  have hb := forest_binomial_mono_rank (by omega : 0 < n) (by simpa only [Fintype.card_coe] using (hB.trans (by omega : A.card+1 ≤ r+1)))
  rw [show n+(r+1)-1=n+r by omega] at hb
  simpa only [Fintype.card_coe] using hb.trans (hcharge.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.sub_le_sub_right hLa 3)))

/-- The original exact-stratum lower bound follows from one scalar
escape condition, with NO doubled-injectivity or half-descent premise.
The collision is paid for by replacing r with r+1 in the charge. -/
theorem stratum_lower_bound_of_escape_ceiling_threshold_with_collision
    {n s q : ℕ} (hq : Odd q) (hn : 4 ≤ n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (b : ZMod (2^s*q)) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hcharge : (n+r).choose (r+1) ≤ 2^((n+r)/(r+1)-3)) :
    stratumBound n s ≤ 2^s*q := by
  classical
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  let A := Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)
  have hA : ∀ i, i ∈ A ↔ ¬ ∃ j, g j=2 • g i+b := by simp [A]
  have hc : A.card=r := hr
  have hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b := by
    intro i hi
    by_contra he
    exact hi ((hA i).mpr he)
  obtain ⟨hlarge,_,_⟩ := escape_ceiling_conditions_of_binomial_charge hn (by omega : 0 < r+1)
    (by simpa only [show n+(r+1)-1=n+r by omega] using hcharge)
  by_contra hnot
  have hacyclic : ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin n, ∀ R : Equiv.Perm (Fin m),
      ¬ (∀ i, g (e (R i))=2 • g (e i)+b) := by
    intro m hm e R hcycle
    have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
    obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) e
      (Fin.castAdd_injective m k) e.injective
    exact hnot (stratum_lower_bound_of_cycle_escape_threshold_with_collision hq hm g hg A b hclosed
      (by simpa only [hc] using hlarge) E R (by simpa only [hE] using hcycle))
  have hbinary : 2^n ≤ Fintype.card (ZMod (2^s*q)) := by
    rcases Nat.even_or_odd (2^s*q) with hev | hod
    · obtain ⟨M,hM⟩ := hev
      have hNM : 2^s*q=2*M := by omega
      exact binary_card_bound_of_acyclic_escape_ceiling_threshold_with_one_collision hn g hg (half_add_half hNM)
        (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hNM u hu) A hc b hA hacyclic hcharge
    · apply binary_card_bound_of_acyclic_escape_ceiling_threshold_with_one_collision hn g hg (h:=0) (by simp) ?_
        A hc b hA hacyclic hcharge
      intro u hu
      left
      apply add_self_injective_zmod hod
      simpa using hu
  rw [ZMod.card] at hbinary
  exact hnot ((Nat.sub_le _ _).trans hbinary)

/-- An unconditional global bound at a single shift's actual scalar
threshold, including tuples with an actual opposite pair. -/
theorem global_lower_bound_of_escape_ceiling_threshold_with_collision
    {n N : ℕ} [NeZero N] (hn : 4 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hcharge : (n+r).choose (r+1) ≤ 2^((n+r)/(r+1)-3)) : globalBound n ≤ N := by
  obtain ⟨s,q,hq,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne N)
  have hh := stratum_lower_bound_of_escape_ceiling_threshold_with_collision hq hn g hg b r hr hcharge
  have hbound : globalBound n ≤ stratumBound n s := by
    unfold globalBound stratumBound
    exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.min_le_right s (Nat.log 2 n))) _
  exact hbound.trans hh

/-- Every original exact-stratum counterexample obeys the r+1
exponential and quadratic-log escape bounds at EVERY shift. Neither
failure of half descent nor absence of an opposite pair is assumed. -/
theorem quantitative_escapes_of_stratum_counterexample_with_ceiling
    {n s q : ℕ} (hq : Odd q) (hn : 4 ≤ n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g) (hsmall : 2^s*q < stratumBound n s)
    (b : ZMod (2^s*q)) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    2^((n+r)/(r+1)-3) < (n+r).choose (r+1) ∧ n < (r+1)^2*(Nat.log 2 n+1)+3*(r+1) := by
  have he : 2^((n+r)/(r+1)-3) < (n+r).choose (r+1) := by
    by_contra hh
    have := stratum_lower_bound_of_escape_ceiling_threshold_with_collision hq hn g hg b r hr (by omega)
    omega
  exact ⟨he,(quantitative_escapes_of_stratum_counterexample_with_collision hq hn g hg hsmall b r hr).2⟩

/-- Every hypothetical global counterexample satisfies a quantitative
escape obstruction, with no separate opposite-pair alternative. -/
theorem quantitative_escapes_of_global_counterexample_with_ceiling
    {n N : ℕ} [NeZero N] (hn : 4 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n)
    (b : ZMod N) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    2^((n+r)/(r+1)-3) < (n+r).choose (r+1) ∧ n < (r+1)^2*(Nat.log 2 n+1)+3*(r+1) := by
  have he : 2^((n+r)/(r+1)-3) < (n+r).choose (r+1) := by
    by_contra hh
    have := global_lower_bound_of_escape_ceiling_threshold_with_collision hn g hg b r hr (by omega)
    omega
  exact ⟨he,(quantitative_escapes_of_global_counterexample_with_collision hn g hg hsmall b r hr).2⟩

/-- Original G3 is excluded by the scalar threshold even in its
opposite-pair branch. This does not extract small escape counts from
arbitrary tuples or assert the unrestricted exceptional obstruction. -/
theorem not_validTuple_exceptional_of_escape_ceiling_threshold_with_collision
    {n : ℕ} (hn : 4 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b : ZMod (2*globalBound (n-1))) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hcharge : (n+r).choose (r+1) ≤ 2^((n+r)/(r+1)-3)) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have hh := global_lower_bound_of_escape_ceiling_threshold_with_collision hn g hg b r hr hcharge
  omega

/-- All hypothetical original G3 tuples obey the quantitative escape
bounds at every shift, including tuples with actual opposite pairs. -/
theorem quantitative_escapes_of_exceptional_tuple_with_ceiling
    {n : ℕ} (hn : 4 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (hg : ValidTuple g)
    (b : ZMod (2*globalBound (n-1))) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    2^((n+r)/(r+1)-3) < (n+r).choose (r+1) ∧ n < (r+1)^2*(Nat.log 2 n+1)+3*(r+1) := by
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  exact quantitative_escapes_of_global_counterexample_with_ceiling hn g hg hsmall b r hr

end MinModulus
