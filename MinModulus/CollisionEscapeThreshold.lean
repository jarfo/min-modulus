import MinModulus.CollisionForest

/-! The scalar escape threshold now proves every exact-stratum and
global bound without doubling injectivity. Paying for at most one
collision replaces r by r+1. Original G3 inherits quantitative bounds
even in the opposite-pair branch; unrestricted G1/G2/G3 remain open. -/

namespace MinModulus
open Finset

/-- The cycle branch pays for the unique possible doubled collision
with one extra escape. No injectivity premise is needed. -/
theorem stratum_lower_bound_of_cycle_escape_threshold_with_collision
    {m k s q : ℕ} (hq : Odd q) (hm : 0 < m)
    (g : Fin (m+k) → ZMod (2^s*q)) (hg : ValidTuple g)
    (A : Finset (Fin (m+k))) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hlarge : 6*(A.card+1) ≤ m+k)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hk := outside_le_affine_cycle_add_escape_count hm g hg A b hclosed E R hcycle
  exact stratum_lower_bound_of_valid_few_escape_affine_cycle (by omega) hq g hg A b hclosed
    (by omega) E R hcycle

/-- The original exact-stratum lower bound follows from one scalar
escape condition, with NO doubled-injectivity or half-descent premise.
The collision is paid for by replacing r with r+1 in the charge. -/
theorem stratum_lower_bound_of_escape_binomial_threshold_with_collision
    {n s q : ℕ} (hq : Odd q) (hn : 4 ≤ n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (b : ZMod (2^s*q)) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hcharge : (n+r).choose (r+1) ≤ 2^(n/(r+1)-3)) :
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
  obtain ⟨hlarge,_,_⟩ := escape_average_conditions_of_binomial_charge hn (by omega : 0 < r+1)
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
      exact binary_card_bound_of_acyclic_escape_threshold_with_one_collision hn g hg (half_add_half hNM)
        (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hNM u hu) A hc b hA hacyclic hcharge
    · apply binary_card_bound_of_acyclic_escape_threshold_with_one_collision hn g hg (h:=0) (by simp) ?_
        A hc b hA hacyclic hcharge
      intro u hu
      left
      apply add_self_injective_zmod hod
      simpa using hu
  rw [ZMod.card] at hbinary
  exact hnot ((Nat.sub_le _ _).trans hbinary)

/-- An unconditional global bound at a single shift's actual scalar
threshold, including tuples with an actual opposite pair. -/
theorem global_lower_bound_of_escape_binomial_threshold_with_collision
    {n N : ℕ} [NeZero N] (hn : 4 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hcharge : (n+r).choose (r+1) ≤ 2^(n/(r+1)-3)) : globalBound n ≤ N := by
  obtain ⟨s,q,hq,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne N)
  have hh := stratum_lower_bound_of_escape_binomial_threshold_with_collision hq hn g hg b r hr hcharge
  have hbound : globalBound n ≤ stratumBound n s := by
    unfold globalBound stratumBound
    exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.min_le_right s (Nat.log 2 n))) _
  exact hbound.trans hh

/-- Every original exact-stratum counterexample obeys the r+1
exponential and quadratic-log escape bounds at EVERY shift. Neither
failure of half descent nor absence of an opposite pair is assumed. -/
theorem quantitative_escapes_of_stratum_counterexample_with_collision
    {n s q : ℕ} (hq : Odd q) (hn : 4 ≤ n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g) (hsmall : 2^s*q < stratumBound n s)
    (b : ZMod (2^s*q)) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    2^(n/(r+1)-3) < (n+r).choose (r+1) ∧ n < (r+1)^2*(Nat.log 2 n+1)+3*(r+1) := by
  have he : 2^(n/(r+1)-3) < (n+r).choose (r+1) := by
    by_contra hh
    have := stratum_lower_bound_of_escape_binomial_threshold_with_collision hq hn g hg b r hr (by omega)
    omega
  refine ⟨he,?_⟩
  exact length_lt_escape_quadratic_log_of_binomial (by omega : 0 < r+1)
    (by simpa only [show n+(r+1)-1=n+r by omega] using he)

/-- Every hypothetical global counterexample satisfies a quantitative
escape obstruction, with no separate opposite-pair alternative. -/
theorem quantitative_escapes_of_global_counterexample_with_collision
    {n N : ℕ} [NeZero N] (hn : 4 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n)
    (b : ZMod N) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    2^(n/(r+1)-3) < (n+r).choose (r+1) ∧ n < (r+1)^2*(Nat.log 2 n+1)+3*(r+1) := by
  have he : 2^(n/(r+1)-3) < (n+r).choose (r+1) := by
    by_contra hh
    have := global_lower_bound_of_escape_binomial_threshold_with_collision hn g hg b r hr (by omega)
    omega
  refine ⟨he,?_⟩
  exact length_lt_escape_quadratic_log_of_binomial (by omega : 0 < r+1)
    (by simpa only [show n+(r+1)-1=n+r by omega] using he)

/-- Original G3 is excluded by the scalar threshold even in its
opposite-pair branch. This does not extract small escape counts from
arbitrary tuples or assert the unrestricted exceptional obstruction. -/
theorem not_validTuple_exceptional_of_escape_binomial_threshold_with_collision
    {n : ℕ} (hn : 4 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b : ZMod (2*globalBound (n-1))) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hcharge : (n+r).choose (r+1) ≤ 2^(n/(r+1)-3)) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have hh := global_lower_bound_of_escape_binomial_threshold_with_collision hn g hg b r hr hcharge
  omega

/-- All hypothetical original G3 tuples obey the quantitative escape
bounds at every shift, including tuples with actual opposite pairs. -/
theorem quantitative_escapes_of_exceptional_tuple_with_collision
    {n : ℕ} (hn : 4 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (hg : ValidTuple g)
    (b : ZMod (2*globalBound (n-1))) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    2^(n/(r+1)-3) < (n+r).choose (r+1) ∧ n < (r+1)^2*(Nat.log 2 n+1)+3*(r+1) := by
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  exact quantitative_escapes_of_global_counterexample_with_collision hn g hg hsmall b r hr

end MinModulus
