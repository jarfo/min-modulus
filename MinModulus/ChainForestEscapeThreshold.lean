import MinModulus.ChainForestFourEscape

/-! Uniform half descent at arbitrary actual escape counts follows
from a single binomial-versus-exponential threshold. Every original
critical no-half tuple therefore has a quadratic logarithmic constraint
on its escape count at every affine shift. No forest, cycle, profile or
seed normal form is supplied. Unrestricted G1/G2/G3 remain open. -/

namespace MinModulus
open Finset

/-- The widest genuine arm pays any rank's packing error whenever
the average-length interval already meets the explicit threshold. -/
theorem binary_card_bound_of_genuine_forest_average_threshold
    {n r : ℕ} (hr0 : 0 < r) {β : Type*} [Fintype β] (hr : Fintype.card β=r)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (havg : 4 ≤ n/r) (hwide : 2*n+1 ≤ 2^(n/r))
    (hcharge : (n+r-1).choose r ≤ 2^(n/r-3)) :
    2^n ≤ Fintype.card G := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hneβ : Finset.univ.Nonempty (α := β) := by
    apply Finset.card_pos.mp
    simpa only [Finset.card_univ,hr] using hr0
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image Finset.univ L hneβ
  have hnL : n ≤ r*L j := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi ↦ hmax i hi)
    simpa only [hsize,Finset.sum_const,Finset.card_univ,smul_eq_mul,hr] using hs
  have hmL : n/r ≤ L j := Nat.div_le_of_le_mul (by simpa only [Nat.mul_comm] using hnL)
  have hcap : 2*n+1 ≤ 2^(L j) :=
    hwide.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hmL)
  have hc : (n+r-1).choose r ≤ 2^(L j-3) :=
    hcharge.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.sub_le_sub_right hmL 3))
  apply binary_card_bound_of_one_genuine_arm_short_interval (by
    have := Nat.div_le_self n r
    omega) L hL g hg E x b hchain j hcap (by omega) _ (hgenuine j)
  simpa only [hr] using hc

/-- For any number of escapes, a sufficiently long tuple forces
every actual cycle into the existing exact-stratum cycle bound. -/
theorem stratum_lower_bound_of_injective_escape_cycle_length_threshold
    {m k s q : ℕ} (hq : Odd q) (hm : 0 < m) (hn : 4 ≤ m+k)
    (g : Fin (m+k) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hlarge : 6*A.card ≤ m+k)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) (s+1) ≤ 2^(s+1)*q := by
  have hk := outside_lt_affine_cycle_add_escapes_of_injective_doubling hm g hg hinj A b hclosed E R hcycle
  exact stratum_lower_bound_of_valid_loss_free_escape_cycle (by omega) hq g hg hinj A b hclosed
    (by omega) E R hcycle

/-- The explicit cycle-length threshold retains arbitrary escape
counts and all actual embeddings, without an outsider-count premise. -/
theorem stratum_lower_bound_of_injective_embedded_escape_cycle_length_threshold
    {n m s q : ℕ} (hq : Odd q) (hm : 0 < m) (hn : 4 ≤ n)
    (g : Fin n → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hlarge : 6*A.card ≤ n)
    (e : Fin m ↪ Fin n) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) : stratumBound n (s+1) ≤ 2^(s+1)*q := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) e
    (Fin.castAdd_injective m k) e.injective
  exact stratum_lower_bound_of_injective_escape_cycle_length_threshold hq hm hn g hg hinj A b hclosed hlarge E R
    (by simpa only [hE] using hcycle)

/-- The explicit cycle-length threshold retains arbitrary escape
counts and all actual embeddings, without an outsider-count premise. -/
theorem admitsValidTuple_half_of_critical_escape_cycle_length_threshold
    {n m s q : ℕ} (hq : Odd q) (hn : 3 ≤ n) (hm : 0 < m)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hlarge : 6*A.card ≤ n+1)
    (e : Fin m ↪ Fin (n+1)) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) : AdmitsValidTuple n (2^s*q) := by
  by_contra hnohalf
  have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  have hi : Function.Injective (fun i ↦ 2 • g i) := by
    apply doubling_injective_of_no_common_touched_witness g hg (half_add_half hN)
      (half_ne_zero hN hM) (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu)
    rintro ⟨j,hj⟩
    exact hnohalf (exists_validTuple_half_of_delete hN hM hg j hj)
  have hb := stratum_lower_bound_of_injective_embedded_escape_cycle_length_threshold hq hm (by omega)
    g hg hi A b hclosed hlarge e R hcycle
  omega

/-- The explicit cycle-length threshold retains arbitrary escape
counts and all actual embeddings, without an outsider-count premise. -/
theorem injective_and_acyclic_of_critical_escape_length_threshold_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hlarge : 6*A.card ≤ n+1)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    Function.Injective (fun i ↦ 2 • g i) ∧
      ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin (n+1), ∀ R : Equiv.Perm (Fin m),
        ¬ (∀ i, g (e (R i))=2 • g (e i)+b) := by
  have hM : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  constructor
  · apply doubling_injective_of_no_common_touched_witness g hg (half_add_half hN)
      (half_ne_zero hN hM) (fun u hu ↦ zmod_eq_zero_or_half_of_add_self_eq_zero hN u hu)
    rintro ⟨j,hj⟩
    exact hnohalf (exists_validTuple_half_of_delete hN hM hg j hj)
  · intro m hm e R hd
    exact hnohalf (admitsValidTuple_half_of_critical_escape_cycle_length_threshold hq hn hm
      g hg hc A b hclosed hlarge e R hd)

/-- Original critical half descent at any actual escape count whose
cycle budget and average-arm binomial threshold both hold. No actual
cycle, forest, seed normal form or profile shape is supplied. -/
theorem admitsValidTuple_half_of_critical_escape_average_threshold
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (b : ZMod (2^(s+1)*q)) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hlarge : 6*r ≤ n+1) (havg : 4 ≤ (n+1)/r)
    (hwide : 2*(n+1)+1 ≤ 2^((n+1)/r))
    (hcharge : (n+r).choose r ≤ 2^((n+1)/r-3)) :
    AdmitsValidTuple n (2^s*q) := by
  classical
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  let B := Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)
  change B.card=r at hr
  have hr0 : 0 < r := by
    have hh := three_le_affine_escape_card_of_critical_without_half hq g hg hc hnohalf b
    have hlo : 3 ≤ B.card := by simpa only [B,not_exists] using hh
    omega
  have hclosedB : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b := by
    intro i hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  obtain ⟨hinj,hacyclic⟩ := injective_and_acyclic_of_critical_escape_length_threshold_without_half
    hq hn g hg hc B b hclosedB (by simpa only [hr] using hlarge) hnohalf
  obtain ⟨L,hL,_,E,x,hchain,hend⟩ :=
    exists_affine_chain_forest_of_injective_acyclic_doubling g hinj B b hclosedB hacyclic
  have hcard : Fintype.card B=r := by simpa only [Fintype.card_coe] using hr
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t ht
    have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
    rw [he] at ht
    exact (Finset.mem_filter.mp a.property).2 ⟨t,ht⟩
  have hh := binary_card_bound_of_genuine_forest_average_threshold hr0 hcard L hL
    g hg E x b hchain hgen havg hwide (by simpa only [show n+1+r-1=n+r by omega] using hcharge)
  rw [ZMod.card] at hh
  have hsub : 2^(s+1)*q < 2^(n+1) := hc.trans_le (Nat.sub_le _ _)
  omega

/-- Every shift of an original critical no-half tuple fails the explicit
four-part arithmetic threshold at its ACTUAL escape count. -/
theorem escape_average_threshold_fails_of_critical_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q))
    (b : ZMod (2^(s+1)*q)) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    ¬ (6*r ≤ n+1 ∧ 4 ≤ (n+1)/r ∧ 2*(n+1)+1 ≤ 2^((n+1)/r) ∧
      (n+r).choose r ≤ 2^((n+1)/r-3)) := by
  rintro ⟨hlarge,havg,hwide,hcharge⟩
  exact hnohalf (admitsValidTuple_half_of_critical_escape_average_threshold
    hq hn g hg hc b r hr hlarge havg hwide hcharge)

/-- The binomial charge alone supplies all width and cycle thresholds
in a nontrivial positive-rank forest. -/
theorem escape_average_conditions_of_binomial_charge
    {n r : ℕ} (hn : 4 ≤ n) (hr : 0 < r)
    (hc : (n+r-1).choose r ≤ 2^(n/r-3)) :
    6*r ≤ n ∧ 4 ≤ n/r ∧ 2*n+1 ≤ 2^(n/r) := by
  have hchoose : n ≤ (n+r-1).choose r := by
    have hh := Nat.choose_le_choose (n-1) (by omega : n ≤ n+r-1)
    have hs : (n+r-1).choose (n-1)=(n+r-1).choose r := by
      simpa only [show n+r-1-r=n-1 by omega] using
        Nat.choose_symm (by omega : r ≤ n+r-1)
    rw [hs] at hh
    have hc1 : n.choose (n-1)=n := by
      rw [Nat.choose_symm (by omega : 1 ≤ n),Nat.choose_one_right]
    simpa only [hc1] using hh
  have hsize := hchoose.trans hc
  have hdiv := Nat.div_le_self n r
  have hlarge : 6 ≤ n/r := by
    by_contra h
    have hp : 2^(n/r-3) ≤ 4 := by
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : n/r-3 ≤ 2)
      norm_num at hh
      exact hh
    have hp' : 2^(n/r-3) ≤ 2 := by
      have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : n/r-3 ≤ 1)
      norm_num at hh
      exact hh
    omega
  have hpow : 2^(n/r)=8*2^(n/r-3) := by
    rw [show n/r=3+(n/r-3) by omega,pow_add]
    norm_num
  refine ⟨?_,by omega,by omega⟩
  exact (Nat.le_div_iff_mul_le hr).mp hlarge

/-- A single explicit binomial inequality at the actual escape count
gives original critical half descent, uniformly in count and stratum. -/
theorem admitsValidTuple_half_of_critical_escape_binomial_threshold
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (b : ZMod (2^(s+1)*q)) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r)
    (hcharge : (n+r).choose r ≤ 2^((n+1)/r-3)) :
    AdmitsValidTuple n (2^s*q) := by
  classical
  by_contra hnohalf
  have hr0 : 0 < r := by
    have hh := three_le_affine_escape_card_of_critical_without_half hq g hg hc hnohalf b
    have hh' : 3 ≤ (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card := by
      simpa only [not_exists] using hh
    rw [hr] at hh'
    omega
  obtain ⟨hlarge,havg,hwide⟩ := escape_average_conditions_of_binomial_charge (by omega : 4 ≤ n+1) hr0
    (by simpa only [show n+1+r-1=n+r by omega] using hcharge)
  exact hnohalf (admitsValidTuple_half_of_critical_escape_average_threshold
    hq hn g hg hc b r hr hlarge havg hwide hcharge)

/-- Every shift of an original critical no-half tuple has enough
actual escapes to violate the exponential-versus-binomial threshold. -/
theorem exponential_lt_escape_binomial_of_critical_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q))
    (b : ZMod (2^(s+1)*q)) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    2^((n+1)/r-3) < (n+r).choose r := by
  by_contra h
  exact hnohalf (admitsValidTuple_half_of_critical_escape_binomial_threshold
    hq hn g hg hc b r hr (by omega))

/-- Failure of the exponential packing threshold forces a quadratic
logarithmic lower constraint on the actual escape count. -/
theorem length_lt_escape_quadratic_log_of_binomial
    {n r : ℕ} (hr : 0 < r)
    (h : 2^(n/r-3) < (n+r-1).choose r) :
    n < r^2*(Nat.log 2 n+1)+3*r := by
  have hnlog := Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  have hpow : (n+r-1).choose r ≤ 2^((Nat.log 2 n+1)*r) := by
    have hc : (n+r-1).choose r ≤ n^r := by
      simpa only [show n+r-1+1-r=n by omega] using Nat.choose_le_sub_pow (n+r-1) r
    have hh := hc.trans (Nat.pow_le_pow_left hnlog.le r)
    simpa only [← pow_mul] using hh
  have hexp : n/r-3 < (Nat.log 2 n+1)*r := by
    by_contra hnot
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega : (Nat.log 2 n+1)*r ≤ n/r-3)
    exact (not_lt_of_ge hh) (h.trans_le hpow)
  have hpos : 0 < (Nat.log 2 n+1)*r := Nat.mul_pos (by omega) hr
  have hdiv : n/r ≤ (Nat.log 2 n+1)*r+2 := by omega
  have hmul := Nat.mul_le_mul_left r hdiv
  have hrem := Nat.mod_lt n hr
  have hsplit := Nat.mod_add_div n r
  nlinarith

/-- In every shift of an original critical no-half tuple, the escape
count grows at least on the square-root-over-logarithm scale. All
counts refer to the original affine doubling graph. -/
theorem length_lt_escape_quadratic_log_of_critical_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q))
    (b : ZMod (2^(s+1)*q)) (r : ℕ)
    (hr : (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card=r) :
    n+1 < r^2*(Nat.log 2 (n+1)+1)+3*r := by
  classical
  have hr0 : 0 < r := by
    have hh := three_le_affine_escape_card_of_critical_without_half hq g hg hc hnohalf b
    have hh' : 3 ≤ (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card := by
      simpa only [not_exists] using hh
    rw [hr] at hh'
    omega
  apply length_lt_escape_quadratic_log_of_binomial hr0
  simpa only [show n+1+r-1=n+r by omega] using
    exponential_lt_escape_binomial_of_critical_without_half hq hn g hg hc hnohalf b r hr

end MinModulus
