import MinModulus.ChainForestBoundaryIntervalSharp

/-! Every genuine four-chain forest from length 101 satisfies the
binary bound. Existing cycle budgets consume four-escape cycles from
length 16. Together these prove original critical half descent with at
most four escapes from parent length 101, in every stratum. Large
no-half tuples have five escapes at every shift; unrestricted G1/G2/G3
and arbitrary escape extraction remain open. -/

namespace MinModulus
open Finset

/-- The exact four-chain packing error is paid from arm length 26. -/
theorem four_length_binomial_le_short_exponential {L : ℕ} (hL : 26 ≤ L) :
    (4*L+3).choose 4 ≤ 2^(L-3) := by
  have hformula : ∀ m : ℕ, 24*(m+3).choose 4=(m+3)*(m+2)*(m+1)*m := by
    intro m
    have hh := Nat.ascFactorial_eq_factorial_mul_choose' m 4
    norm_num [Nat.ascFactorial_succ,Nat.ascFactorial_zero,
      show m+4-1=m+3 by omega] at hh
    nlinarith
  induction L, hL using Nat.le_induction with
  | base =>
    have hh := hformula 104
    norm_num at hh ⊢
    omega
  | succ L hL ih =>
    have ha := hformula (4*L)
    have hb := hformula (4*(L+1))
    have hsq := Nat.mul_le_mul_right L hL
    have hcube := Nat.mul_le_mul_right (L*L) hL
    have hquartic := Nat.mul_le_mul_right (L*L*L) hL
    have hstep : (4*(L+1)+3).choose 4 ≤ 2*(4*L+3).choose 4 := by nlinarith
    calc
      _ ≤ 2*(4*L+3).choose 4 := hstep
      _ ≤ 2*2^(L-3) := Nat.mul_le_mul_left 2 ih
      _ = 2^(L+1-3) := by rw [show L+1-3=(L-3)+1 by omega,pow_succ']

/-- Every genuine four-chain forest from parent length 101 satisfies
the binary lower bound in an arbitrary finite abelian group. -/
theorem binary_card_bound_of_genuine_four_chain_forest
    {n : ℕ} (hn : 101 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=4)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  classical
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hneβ : Finset.univ.Nonempty (α := β) := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ,hr]
    decide
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image Finset.univ L hneβ
  have hnL : n ≤ 4*L j := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi ↦ hmax i hi)
    simpa only [hsize,Finset.sum_const,Finset.card_univ,smul_eq_mul,hr] using hs
  have hLj : 26 ≤ L j := by omega
  have hbinom := four_length_binomial_le_short_exponential hLj
  have hlin := Nat.lt_two_pow_self (n := L j-4)
  have hpow : 2^(L j)=16*2^(L j-4) := by
    rw [show L j=4+(L j-4) by omega,pow_add]
    norm_num
  apply binary_card_bound_of_one_genuine_arm_short_interval (by omega) L hL g hg E x b hchain
    j (by omega) (by omega) _ (hgenuine j)
  simp only [hr,show n+4-1=n+3 by omega]
  exact (Nat.choose_le_choose 4 (by omega : n+3 ≤ 4*L j+3)).trans hbinom

/-- At parent length at least sixteen, a four-escape cycle must
be large enough for the existing loss-free exact-stratum bound. -/
theorem stratum_lower_bound_of_injective_four_escape_affine_cycle
    {m k s q : ℕ} (hq : Odd q) (hm : 0 < m) (hn : 16 ≤ m+k)
    (g : Fin (m+k) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin (m+k))) (hA : A.card ≤ 4) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (E : Equiv.Perm (Fin (m+k))) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) (s+1) ≤ 2^(s+1)*q := by
  have hk := outside_lt_affine_cycle_add_escapes_of_injective_doubling hm g hg hinj A b hclosed E R hcycle
  have hm7 : 7 ≤ m := by omega
  exact stratum_lower_bound_of_valid_loss_free_escape_cycle (by omega) hq g hg hinj A b hclosed
    (by omega) E R hcycle

/-- The original four-escape cycle data are consumed from parent
length sixteen; all embeddings and affine data are retained. -/
theorem stratum_lower_bound_of_injective_four_escape_embedded_affine_cycle
    {n m s q : ℕ} (hq : Odd q) (hm : 0 < m) (hn : 16 ≤ n)
    (g : Fin n → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset (Fin n)) (hA : A.card ≤ 4) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (e : Fin m ↪ Fin n) (R : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b) : stratumBound n (s+1) ≤ 2^(s+1)*q := by
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) e
    (Fin.castAdd_injective m k) e.injective
  exact stratum_lower_bound_of_injective_four_escape_affine_cycle hq hm hn g hg hinj A hA b hclosed E R
    (by simpa only [hE] using hcycle)


/-- The original four-escape cycle data are consumed from parent
length sixteen; all embeddings and affine data are retained. -/
theorem admitsValidTuple_half_of_critical_four_escape_affine_cycle
    {n m s q : ℕ} (hq : Odd q) (hn : 15 ≤ n) (hm : 0 < m)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 4) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
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
  have hb := stratum_lower_bound_of_injective_four_escape_embedded_affine_cycle hq hm (by omega)
    g hg hi A hA b hclosed e R hcycle
  omega


/-- The original four-escape cycle data are consumed from parent
length sixteen; all embeddings and affine data are retained. -/
theorem injective_and_acyclic_of_critical_four_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 15 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 4) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
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
    exact hnohalf (admitsValidTuple_half_of_critical_four_escape_affine_cycle hq hn hm
      g hg hc A hA b hclosed e R hd)


/-- Every original critical four-escape case gives half descent
from parent length 101: cycles and the actual four-chain forest are
both consumed without supplied normal forms or seed restrictions. -/
theorem admitsValidTuple_half_of_critical_four_escape_large
    {n s q : ℕ} (hq : Odd q) (hn : 100 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 4) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b) :
    AdmitsValidTuple n (2^s*q) := by
  classical
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hinj,hacyclic⟩ := injective_and_acyclic_of_critical_four_escape_without_half
    hq (by omega) g hg hc A hA b hclosed hnohalf
  let B := Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)
  have hBA : B ⊆ A := by
    intro i hi
    by_contra hnot
    exact (Finset.mem_filter.mp hi).2 (hclosed i hnot)
  have hcard : B.card=4 := by
    have hlo := four_le_affine_escape_card_of_critical_without_half_of_length_ge_52
      hq (by omega) g hg hc hnohalf b
    have hhi := (Finset.card_le_card hBA).trans hA
    change 4 ≤ B.card at hlo
    omega
  have hclosedB : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b := by
    intro i hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  obtain ⟨L,hL,_,E,x,hchain,hend⟩ :=
    exists_affine_chain_forest_of_injective_acyclic_doubling g hinj B b hclosedB hacyclic
  have hr : Fintype.card B=4 := by simpa only [Fintype.card_coe] using hcard
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t ht
    have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
    rw [he] at ht
    exact (Finset.mem_filter.mp a.property).2 ⟨t,ht⟩
  have hh := binary_card_bound_of_genuine_four_chain_forest (by omega) hr L hL g hg E x b hchain hgen
  rw [ZMod.card] at hh
  have hsub : 2^(s+1)*q < 2^(n+1) := hc.trans_le (Nat.sub_le _ _)
  omega

/-- Every critical no-half tuple from parent length 101 has at least
five actual affine-doubling escapes at every shift. -/
theorem five_le_affine_escape_card_of_large_critical_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 100 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) (b : ZMod (2^(s+1)*q)) :
    5 ≤ (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card := by
  classical
  by_contra hnot
  let A := Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)
  have hA : A.card ≤ 4 := by dsimp only [A]; omega
  have hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b := by
    intro i hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  exact hnohalf (admitsValidTuple_half_of_critical_four_escape_large hq hn g hg hc A hA b hclosed)

end MinModulus
