import MinModulus.OddEscapeThreshold

/-! Every hypothetical global counterexample has an actual opposite
pair or satisfies the quantitative escape obstruction at every shift.
The original exceptional G3 input inherits this split, and its actual
injective-doubling branch is excluded by the scalar threshold. The
opposite-pair branch remains; unrestricted G1/G2/G3 are still open. -/

namespace MinModulus
open Finset

/-- Actual injective doubling and the scalar escape threshold force
the global conjectured bound, without any global-gate assumption. -/
theorem global_lower_bound_of_injective_escape_binomial_threshold
    {n N : ℕ} [NeZero N] (hn : 4 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (b : ZMod N) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hcharge : (n+r-1).choose r ≤ 2^(n/r-3)) :
    globalBound n ≤ N := by
  obtain ⟨s,q,hq,rfl⟩ := Nat.exists_eq_two_pow_mul_odd (NeZero.ne N)
  have hh := stratum_lower_bound_of_injective_escape_binomial_threshold hq hn g hg hinj b r hr hcharge
  have hbound : globalBound n ≤ stratumBound n s := by
    unfold globalBound stratumBound
    exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.min_le_right s (Nat.log 2 n))) _
  exact hbound.trans hh

/-- A global counterexample with injective actual doubling violates
the numerical threshold at every affine shift. -/
theorem exponential_lt_escape_binomial_of_injective_global_counterexample
    {n N : ℕ} [NeZero N] (hn : 4 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (b : ZMod N) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    2^(n/r-3) < (n+r-1).choose r := by
  by_contra hnot
  have hh := global_lower_bound_of_injective_escape_binomial_threshold hn g hg hinj b r hr (by omega)
  omega

/-- Every hypothetical global counterexample either has an actual
doubled collision, or obeys the quantitative escape constraint at all
shifts. No G1, G2 or G3 premise is assumed. -/
theorem doubled_collision_or_quantitative_escapes_of_global_counterexample
    {n N : ℕ} [NeZero N] (hn : 4 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n) :
    (∃ i j, i ≠ j ∧ 2 • g i=2 • g j) ∨
      ∀ (b : ZMod N) (r : ℕ),
        (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
        2^(n/r-3) < (n+r-1).choose r ∧ n < r^2*(Nat.log 2 n+1)+3*r := by
  classical
  by_cases hinj : Function.Injective (fun i ↦ 2 • g i)
  · right
    intro b r hr
    have hh := exponential_lt_escape_binomial_of_injective_global_counterexample hn g hg hsmall hinj b r hr
    have hr0 : 0 < r := by
      by_contra hz
      have hrz : r=0 := by omega
      rw [hrz] at hh
      norm_num at hh
    exact ⟨hh,length_lt_escape_quadratic_log_of_binomial hr0 hh⟩
  · left
    by_contra hnot
    apply hinj
    intro i j he
    by_contra hne
    exact hnot ⟨i,j,hne,he⟩

/-- An actual doubled collision in a valid cyclic tuple is an
opposite pair at an even modulus, with a positive half modulus. -/
theorem opposite_pair_of_valid_doubled_collision
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (i j : Fin n) (hne : i ≠ j) (heq : 2 • g i=2 • g j) :
    ∃ M : ℕ, 0 < M ∧ N=2*M ∧ g i=g j+(M : ZMod N) := by
  have hev : Even N := by
    rcases Nat.even_or_odd N with hN | hN
    · exact hN
    · exfalso
      apply hne
      apply validTuple_injective g hg
      apply add_self_injective_zmod hN
      simpa only [two_nsmul] using heq
  obtain ⟨M,hM⟩ := hev
  have hN : N=2*M := by omega
  have hMp : 0 < M := by have := Nat.pos_of_ne_zero (NeZero.ne N); omega
  refine ⟨M,hMp,hN,?_⟩
  have hu : (g i-g j)+(g i-g j)=0 := by
    have hh : 2 • (g i-g j)=0 := by rw [smul_sub,heq,sub_self]
    simpa only [two_nsmul] using hh
  rcases zmod_eq_zero_or_half_of_add_self_eq_zero hN (g i-g j) hu with hz | hh
  · exact (hne (validTuple_injective g hg (sub_eq_zero.mp hz))).elim
  · simpa only [add_comm] using (sub_eq_iff_eq_add.mp hh)

/-- Every global counterexample has an actual opposite pair or obeys
the quantitative escape obstruction at all shifts. -/
theorem opposite_pair_or_quantitative_escapes_of_global_counterexample
    {n N : ℕ} [NeZero N] (hn : 4 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < globalBound n) :
    (∃ M : ℕ, 0 < M ∧ N=2*M ∧ ∃ i j, i ≠ j ∧ g i=g j+(M : ZMod N)) ∨
      ∀ (b : ZMod N) (r : ℕ),
        (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
        2^(n/r-3) < (n+r-1).choose r ∧ n < r^2*(Nat.log 2 n+1)+3*r := by
  rcases doubled_collision_or_quantitative_escapes_of_global_counterexample hn g hg hsmall with ⟨i,j,hne,heq⟩ | hquant
  · obtain ⟨M,hMp,hM,hh⟩ := opposite_pair_of_valid_doubled_collision g hg i j hne heq
    exact Or.inl ⟨M,hMp,hM,i,j,hne,hh⟩
  · exact Or.inr hquant

/-- The exceptional G3 modulus is excluded by the scalar escape
threshold whenever actual tuple doubling is injective. -/
theorem not_validTuple_exceptional_of_injective_escape_binomial_threshold
    {n : ℕ} (hn : 4 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (b : ZMod (2*globalBound (n-1))) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hcharge : (n+r-1).choose r ≤ 2^(n/r-3)) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have hh := global_lower_bound_of_injective_escape_binomial_threshold hn g hg hinj b r hr hcharge
  omega

/-- Original exceptional G3 data retain an actual opposite pair, or
the full quantitative escape obstruction at every affine shift. No
injectivity or no-half-child assumption is supplied. -/
theorem opposite_pair_or_quantitative_escapes_of_exceptional_tuple
    {n : ℕ} (hn : 4 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (hg : ValidTuple g) :
    (∃ i j, i ≠ j ∧ g i=g j+(globalBound (n-1) : ZMod (2*globalBound (n-1)))) ∨
      ∀ (b : ZMod (2*globalBound (n-1))) (r : ℕ),
        (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r →
        2^(n/r-3) < (n+r-1).choose r ∧ n < r^2*(Nat.log 2 n+1)+3*r := by
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  rcases opposite_pair_or_quantitative_escapes_of_global_counterexample hn g hg hsmall with ⟨M,_,hM,i,j,hne,hh⟩ | hquant
  · have he : M=globalBound (n-1) := by omega
    exact Or.inl ⟨i,j,hne,by simpa only [he] using hh⟩
  · exact Or.inr hquant

end MinModulus
