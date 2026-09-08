import MinModulus.ChainForestBoundaryInterval

/-! A strict eighth-width exterior interval pays the exact binomial
packing error for every genuine three-chain forest from length 52.
The original critical three-escape case gives half descent in every
stratum in this range. This lowers the previous threshold of 67;
unrestricted G1/G2/G3 and arbitrary escape extraction remain open. -/

namespace MinModulus
open Finset

/-- Excluding the all-ones tail nearly doubles the available interval. -/
theorem exists_binary_rep_twice_width_add_short
    {L v : ℕ} (hL : 4 ≤ L) (hv : 0 < v) (hsmall : v < 2^(L-3)) :
    ∃ u, Supp L u ∧ val L u=2*2^L-1+v ∧ dsum L u ≤ L := by
  obtain ⟨u,hs,hu,hdu⟩ := exists_rep_lt (L-3) (v-1) (by omega)
  have hsL := supp_mono (by omega : L-3 ≤ L) hs
  obtain ⟨w,hws,hw,hwd⟩ := exists_binary_rep_add_two_top_coins (by omega : 0 < L) u hsL
  obtain ⟨z,hzs,hz,hzd⟩ := exists_binary_rep_add_two_top_coins (by omega : 0 < L) w hws
  refine ⟨z,hzs,?_,?_⟩
  · rw [hz,hw,val_pad (by omega : L-3 ≤ L) hs,hu]
    have hp : 0 < 2^L := by positivity
    omega
  · rw [hzd,hwd,dsum_pad (by omega : L-3 ≤ L) hs]
    omega

/-- The exact three-chain binomial error is already exponential
at maximum arm length eighteen, without the coarser cubic estimate. -/
theorem three_length_binomial_le_short_exponential {L : ℕ} (hL : 18 ≤ L) :
    (3*L+2).choose 3 ≤ 2^(L-3) := by
  have hformula : ∀ m : ℕ, 6*(m+2).choose 3=(m+2)*(m+1)*m := by
    intro m
    have hh := Nat.ascFactorial_eq_factorial_mul_choose' m 3
    norm_num [Nat.ascFactorial_succ,Nat.ascFactorial_zero,
      show m+3-1=m+2 by omega] at hh
    nlinarith
  induction L, hL using Nat.le_induction with
  | base =>
    have hh := hformula 54
    norm_num at hh ⊢
    omega
  | succ L hL ih =>
    have ha := hformula (3*L)
    have hb := hformula (3*(L+1))
    have hsq := Nat.mul_le_mul_right L hL
    have hcube := Nat.mul_le_mul_right (L*L) hL
    have hstep : (3*(L+1)+2).choose 3 ≤ 2*(3*L+2).choose 3 := by nlinarith
    calc
      _ ≤ 2*(3*L+2).choose 3 := hstep
      _ ≤ 2*2^(L-3) := Nat.mul_le_mul_left 2 ih
      _ = 2^(L+1-3) := by rw [show L+1-3=(L-3)+1 by omega,pow_succ']

/-- A strict eighth-width deficit fits the full rival budget. -/
theorem not_validTuple_of_short_boundary_axis_collision
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (_hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n ≤ 2^(L a)) (hLa : 4 ≤ L a)
    (t : ℕ) (p : β → ℕ) (hp : ∀ i, p i < 2^(L i))
    (hpa : p a < t) (ht : t-p a < 2^(L a-3))
    (heq : (∑ i, p i • x i)=2^(L a) • x a+t • x a) : ¬ ValidTuple g := by
  classical
  let X := fun i ↦ 2^(L i)-1-p i+(if i=a then 2^(L a)+t else 0)
  have hXa : X a=2*2^(L a)-1+(t-p a) := by
    simp only [X,if_true]
    have := hp a
    have h : 0 < 2^(L a) := by positivity
    omega
  have hrep : ∀ i, ∃ u, val (L i) u=X i ∧ dsum (L i) u ≤ L i := by
    intro i
    by_cases hi : i=a
    · subst i
      obtain ⟨u,_,hu,hdu⟩ := exists_binary_rep_twice_width_add_short hLa (by omega : 0 < t-p a) ht
      exact ⟨u,hu.trans hXa.symm,hdu⟩
    · obtain ⟨u,_,hu,hdu⟩ := exists_rep_le (L i) (2^(L i)-1-p i) (by
        have h : 0 < 2^(L i) := by positivity
        omega)
      exact ⟨u,by simpa only [X,if_neg hi,add_zero] using hu,hdu⟩
  choose u hu hcost using hrep
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hlow : (∑ i, dsum (L i) (u i)) ≤ n := by
    simpa only [hsize] using Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hcost i)
  have hhigh : n ≤ ∑ i, X i := by
    have hh := Finset.single_le_sum (f := X) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    rw [hXa] at hh
    have h : 0 < 2^(L a) := by positivity
    omega
  have hneq : ∃ i, X i ≠ 2^(L i)-1 := by
    refine ⟨a,?_⟩
    rw [hXa]
    have h : 0 < 2^(L a) := by positivity
    omega
  have hsum : (∑ i, X i • x i)=∑ i, (2^(L i)-1) • x i := by
    have hb : (∑ i, (if i=a then 2^(L a)+t else 0) • x i)=2^(L a) • x a+t • x a := by
      simp only [ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true,add_nsmul]
    simp only [X,add_nsmul,Finset.sum_add_distrib,hb,← heq]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← add_nsmul,Nat.sub_add_cancel (by have := hp i; omega)]
  exact not_validTuple_of_chain_forest_integer_weights L X g E x b hchain u hu hlow hhigh hneq hsum


/-- The entire strict eighth-width interval is outside the ordinary box. -/
theorem short_axis_interval_not_in_box_of_long_genuine_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : n ≤ 2^(L a)) (hLa : 4 ≤ L a) (hnz : 2^(L a) • x a ≠ 0)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (t : ℕ) (ht : t < 2^(L a-3))
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i)) :
    (∑ i, p i • x i) ≠ 2^(L a) • x a+t • x a := by
  classical
  intro heq
  have hpa : p a < t := by
    by_contra hnot
    let P := fun i ↦ if i=a then p a-t else p i
    have hP : ∀ i, P i < 2^(L i) := by
      intro i
      by_cases hi : i=a
      · subst i; simpa only [P,if_pos rfl] using (Nat.sub_le (p a) t).trans_lt (hp a)
      · simpa only [P,if_neg hi] using hp i
    have hsum : (∑ i, P i • x i)+t • x a=∑ i, p i • x i := by
      have hs : ∀ i, p i • x i=P i • x i+(if i=a then t • x a else 0) := by
        intro i
        by_cases hi : i=a
        · subst i
          simp only [P,if_pos rfl,if_true]
          rw [← add_nsmul,Nat.sub_add_cancel (by omega)]
        · simp only [P,if_neg hi,add_zero]
      calc
        _=∑ i, (P i • x i+(if i=a then t • x a else 0)) := by
          simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
        _=_ := (Finset.sum_congr rfl (fun i _ ↦ hs i)).symm
    have hrep : (∑ i, P i • x i)=2^(L a) • x a := add_right_cancel (hsum.trans heq)
    exact long_genuine_boundary_not_in_box_of_nonzero L hL g hg E x b hchain a ha hnz hgenuine P hP hrep
  exact not_validTuple_of_short_boundary_axis_collision L hL g E x b hchain a ha hLa t p hp hpa (by omega) heq hg


/-- A strict eighth-width interval pays against the full binomial error. -/
theorem wide_boundary_short_interval_charged_card_bound
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (a : β) (ha : 2*n+1 ≤ 2^(L a)) (hLa : 4 ≤ L a)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n+(2^(L a-3)) ≤ Fintype.card G+(n+Fintype.card β-1).choose (Fintype.card β) := by
  classical
  have hpow : 2^(L a)=8*2^(L a-3) := by
    rw [show L a=3+(L a-3) by omega,pow_add]
    norm_num
  have hnz := boundary_ne_zero_of_subbinary_wide_arm L hL g hg E x b hchain hsub a ha
  let f : Fin (2^(L a-3)) → G := fun t ↦ 2^(L a) • x a+t.val • x a
  have hi : Function.Injective f := by
    intro t u he
    exact seed_interval_injective_of_wide_axis L hL g hg E x b hchain a (2^(L a-3))
      (by omega) (add_left_cancel he)
  let F := Finset.univ.image f
  have hcard : F.card=2^(L a-3) := by
    simp only [F,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]
  have havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) → (∑ i, p i • x i) ≠ z := by
    intro z hz p hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
    exact short_axis_interval_not_in_box_of_long_genuine_boundary L hL g hg E x b hchain a
      (by omega) hLa hnz hgenuine t.val (by have := t.isLt; omega) p hp
  have hh := binomial_gap_with_avoided_set_of_valid_chain_forest hn L hL g hg E x b hchain F havoid
  simpa only [hcard] using hh


/-- One genuine arm whose larger interval pays the error forces the binary bound. -/
theorem binary_card_bound_of_one_genuine_arm_short_interval
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 2*n+1 ≤ 2^(L a)) (hLa : 4 ≤ L a)
    (hcharge : (n+Fintype.card β-1).choose (Fintype.card β) ≤ 2^(L a-3))
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  by_contra hnot
  have hh := wide_boundary_short_interval_charged_card_bound hn L hL g hg E x b hchain
    (by omega) a ha hLa hgenuine
  omega


/-- The exact binomial estimate lowers the unconditional genuine
three-chain binary threshold to parent length 52. -/
theorem binary_card_bound_of_genuine_three_chain_forest_of_length_ge_52
    {n : ℕ} (hn : 52 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
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
  have hnL : n ≤ 3*L j := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi ↦ hmax i hi)
    simpa only [hsize,Finset.sum_const,Finset.card_univ,smul_eq_mul,hr] using hs
  have hLj : 18 ≤ L j := by omega
  have hbinom := three_length_binomial_le_short_exponential hLj
  have hlin := Nat.lt_two_pow_self (n := L j-3)
  have hpow : 2^(L j)=8*2^(L j-3) := by
    rw [show L j=3+(L j-3) by omega,pow_add]
    norm_num
  apply binary_card_bound_of_one_genuine_arm_short_interval (by omega) L hL g hg E x b hchain
    j (by omega) (by omega) _ (hgenuine j)
  simp only [hr,show n+3-1=n+2 by omega]
  exact (Nat.choose_le_choose 3 (by omega : n+2 ≤ 3*L j+2)).trans hbinom


/-- Original critical three-escape data give half descent in every
stratum from parent length 52, with no supplied forest or profile data. -/
theorem admitsValidTuple_half_of_critical_three_escape_of_length_ge_52
    {n s q : ℕ} (hq : Odd q) (hn : 51 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b) :
    AdmitsValidTuple n (2^s*q) := by
  classical
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,_,E,x,hchain,hend,hgenuine,_,_⟩ :=
    exists_spanning_three_chain_forest_of_critical_without_half hq (by omega) g hg hc A hA b hclosed hnohalf
  have hr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t
    have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
    rw [he]
    exact hgenuine a t
  have hh := binary_card_bound_of_genuine_three_chain_forest_of_length_ge_52 (by omega) hr L hL g hg E x b hchain hgen
  rw [ZMod.card] at hh
  have hsub : 2^(s+1)*q < 2^(n+1) := hc.trans_le (Nat.sub_le _ _)
  omega


/-- Every critical no-half tuple from parent length 52 has at least
four actual affine-doubling escapes at every shift. -/
theorem four_le_affine_escape_card_of_critical_without_half_of_length_ge_52
    {n s q : ℕ} (hq : Odd q) (hn : 51 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) (b : ZMod (2^(s+1)*q)) :
    4 ≤ (Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)).card := by
  classical
  by_contra hnot
  let A := Finset.univ.filter (fun i ↦ ¬ ∃ j, g j=2 • g i+b)
  have hA : A.card ≤ 3 := by dsimp only [A]; omega
  have hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b := by
    intro i hi
    by_contra h
    exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
  exact hnohalf (admitsValidTuple_half_of_critical_three_escape_of_length_ge_52 hq hn g hg hc A hA b hclosed)


end MinModulus
