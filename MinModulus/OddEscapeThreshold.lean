import MinModulus.ChainForestEscapeThreshold

/-! Actual injective doubling gives every exact-stratum bound under
one binomial escape-count condition, including zero escapes. In odd
moduli injectivity is automatic, so original odd counterexamples have
the same exponential and quadratic-log escape constraints as critical
G1 no-half tuples. The unrestricted G1/G2/G3 gates remain open. -/

namespace MinModulus
open Finset

/-- The length-versus-escape cycle cutoff works in every exact stratum,
including the odd stratum, whenever actual doubling is injective. -/
theorem stratum_lower_bound_of_injective_cycle_escape_threshold
    {m k s q : ℕ} (hq : Odd q) (hm : 0 < m) (hn : 4 ≤ m+k)
    (g : Fin (m+k) → ZMod (2^s*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hlarge : 6*A.card ≤ m+k)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) s ≤ 2^s*q := by
  have hk := outside_lt_affine_cycle_add_escapes_of_injective_doubling hm g hg hinj A b hclosed E R hcycle
  exact stratum_lower_bound_of_valid_loss_free_escape_cycle (by omega) hq g hg hinj A b hclosed
    (by omega) E R hcycle

/-- Actual cycle embeddings supply their own complement and permutation. -/
theorem stratum_lower_bound_of_injective_embedded_cycle_escape_threshold
    {n m s q : ℕ} (hq : Odd q) (hm : 0 < m) (hn : 4 ≤ n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (b : ZMod (2^s*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hlarge : 6*A.card ≤ n)
    (e : Fin m ↪ Fin n) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) : stratumBound n s ≤ 2^s*q := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) e
    (Fin.castAdd_injective m k) e.injective
  exact stratum_lower_bound_of_injective_cycle_escape_threshold hq hm hn g hg hinj A b hclosed hlarge E R
    (by simpa only [hE] using hcycle)

/-- A single binomial condition gives every exact-stratum bound for
actual injective doubling, including the zero-escape case. -/
theorem stratum_lower_bound_of_injective_escape_binomial_threshold
    {n s q : ℕ} (hq : Odd q) (hn : 4 ≤ n)
    (g : Fin n → ZMod (2^s*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (b : ZMod (2^s*q)) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hcharge : (n+r-1).choose r ≤ 2^(n/r-3)) :
    stratumBound n s ≤ 2^s*q := by
  classical
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  let B := Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)
  change B.card=r at hr
  have hclosedB : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b := by
    intro i hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  by_cases hz : r=0
  · have hB : B=∅ := Finset.card_eq_zero.mp (hr.trans hz)
    exact stratum_lower_bound_of_valid_one_escape_affine_doubling (by omega) hq g hg
      ⟨0,by omega⟩ b (by intro i _; exact hclosedB i (by simp [hB]))
  have hr0 : 0 < r := by omega
  obtain ⟨hlarge,havg,hwide⟩ := escape_average_conditions_of_binomial_charge hn hr0 hcharge
  by_contra hnot
  have hacyclic : ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin n, ∀ R : Equiv.Perm (Fin m),
      ¬ (∀ i, g (e (R i))=2 • g (e i)+b) := by
    intro m hm e R hcycle
    exact hnot (stratum_lower_bound_of_injective_embedded_cycle_escape_threshold hq hm hn g hg hinj
      B b hclosedB (by simpa only [hr] using hlarge) e R hcycle)
  obtain ⟨L,hL,_,E,x,hchain,hend⟩ :=
    exists_affine_chain_forest_of_injective_acyclic_doubling g hinj B b hclosedB hacyclic
  have hcard : Fintype.card B=r := by simpa only [Fintype.card_coe] using hr
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t ht
    have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
    rw [he] at ht
    exact (Finset.mem_filter.mp a.property).2 ⟨t,ht⟩
  have hh := binary_card_bound_of_genuine_forest_average_threshold hr0 hcard L hL
    g hg E x b hchain hgen havg hwide hcharge
  rw [ZMod.card] at hh
  have hs : stratumBound n s ≤ 2^n := Nat.sub_le _ _
  omega

/-- Odd-modulus doubling is automatically injective, so the same
single numerical escape condition proves the original odd threshold. -/
theorem odd_lower_bound_of_escape_binomial_threshold
    {n N : ℕ} (hN : Odd N) (hn : 4 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b : ZMod N) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hcharge : (n+r-1).choose r ≤ 2^(n/r-3)) :
    2^n-1 ≤ N := by
  letI : NeZero N := ⟨hN.pos.ne'⟩
  have hinj : Function.Injective (fun i ↦ 2 • g i) := by
    intro i j he
    apply validTuple_injective g hg
    apply add_self_injective_zmod hN
    simpa only [two_nsmul] using he
  have hh := stratum_lower_bound_of_injective_escape_binomial_threshold (n:=n) (s:=0) (q:=N) hN hn
  rw [show 2^0*N=N by simp] at hh
  simpa only [stratumBound,Nat.zero_min,pow_zero] using hh g hg hinj b r hr hcharge

/-- Every actual affine escape count of an original odd counterexample
violates the same explicit exponential-versus-binomial threshold. -/
theorem exponential_lt_escape_binomial_of_odd_counterexample
    {n N : ℕ} (hN : Odd N) (hn : 4 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < 2^n-1)
    (b : ZMod N) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    2^(n/r-3) < (n+r-1).choose r := by
  by_contra hnot
  have hh := odd_lower_bound_of_escape_binomial_threshold hN hn g hg b r hr (by omega)
  omega

/-- The quadratic logarithmic escape constraint now applies to every
shift of an original odd-modulus counterexample, without a G1 premise. -/
theorem length_lt_escape_quadratic_log_of_odd_counterexample
    {n N : ℕ} (hN : Odd N) (hn : 4 ≤ n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsmall : N < 2^n-1)
    (b : ZMod N) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    n < r^2*(Nat.log 2 n+1)+3*r := by
  have hh := exponential_lt_escape_binomial_of_odd_counterexample hN hn g hg hsmall b r hr
  have hr0 : 0 < r := by
    by_contra hz
    have hrz : r=0 := by omega
    rw [hrz] at hh
    norm_num at hh
  exact length_lt_escape_quadratic_log_of_binomial hr0 hh

end MinModulus
