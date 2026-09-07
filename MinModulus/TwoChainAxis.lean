import MinModulus.G1TwoChainParity

/-! Odd-seed arithmetic eliminates axis corners rather than assuming
both coordinates of the extracted rectangle relation are positive. -/

namespace MinModulus
open Finset

/-- A uniform elementary binary growth estimate for the short-arm cases. -/
theorem five_mul_pred_le_two_pow_of_four_le
    {L : ℕ} (hL : 4 ≤ L) : 5*(L-1) ≤ 2^L := by
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]
    simp only [Nat.add_sub_cancel]
    have hpred : L-1+1=L := by omega
    nlinarith

/-- Six total coordinates make a whole binary side too large to fit
an odd-index axis corner. There is no assumed balance between arms. -/
theorem two_chain_axis_corner_binary_inequality
    {A L : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 6 ≤ A+L) :
    (2^A+1)*(A+L+1-2^A) ≤ 2^L := by
  by_cases hA3 : 3 ≤ A
  · have aux : ∀ k : ℕ, 3 ≤ k → 2*k+1 ≤ 2^k := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => norm_num
      | succ k hk ih => rw [pow_succ]; nlinarith
    have hK := aux A hA3
    by_cases hAL : A ≤ L
    · obtain ⟨B,rfl⟩ := Nat.exists_eq_add_of_le hAL
      have hsub : A+(A+B)+1-2^A ≤ B := by omega
      have hpow : 2*B ≤ 2^B := Nat.mul_le_pow (by decide : 2 ≠ 1) B
      have hKpos : 0 < 2^A := by positivity
      rw [pow_add]
      have hh := Nat.mul_le_mul_left (2^A+1) hsub
      nlinarith
    · have hzero : A+L+1-2^A=0 := by omega
      simp [hzero]
  · have hL4 : 4 ≤ L := by omega
    have hh := five_mul_pred_le_two_pow_of_four_le hL4
    interval_cases A
    · norm_num
      have hs : 1+L+1-2=L := by omega
      rw [hs]
      omega
    · norm_num
      have hs : 2+L+1-4=L-1 := by omega
      rw [hs]
      exact hh

/-- A nonzero axis relation inside the binary rectangle is the seed's
EXACT additive order: any smaller order would be a second zero relation. -/
theorem axis_relation_eq_addOrderOf_of_valid_two_chains
    {A L u : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 5 ≤ A+L)
    {G : Type*} [AddCommGroup G] [Finite G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hu : 0 < u) (huL : u < 2^L) (hzero : u • y=0) : u=addOrderOf y := by
  have ho : 0 < addOrderOf y := addOrderOf_pos y
  have hou : addOrderOf y ≤ u := Nat.le_of_dvd hu (addOrderOf_dvd_of_nsmul_eq_zero hzero)
  have hAp : 0 < 2^A := by positivity
  exact (unique_nonzero_rectangle_relation_of_valid_two_chains hA hL
    (two_chain_rectangle_wide_of_five_le hn) g hg x y hleft hright
    hAp huL (Or.inr (by omega)) hAp (by omega : addOrderOf y < 2^L) (Or.inr ho.ne')
    (by simpa only [zero_nsmul,zero_add] using hzero)
    (by simp only [zero_nsmul,zero_add,addOrderOf_nsmul_eq_zero])).2

/-- An odd canonical representative in a cyclic group has an ODD
index over its additive order, even when it is not a full cyclic unit. -/
theorem exists_odd_index_over_addOrderOf_of_odd_val
    {N : ℕ} [NeZero N] (y : ZMod N) (hy : Odd y.val) :
    ∃ q : ℕ, Odd q ∧ N=addOrderOf y*q := by
  refine ⟨N.gcd y.val,hy.of_dvd_nat (Nat.gcd_dvd_right N y.val),?_⟩
  have ho : addOrderOf y=N/(N.gcd y.val) := by
    simpa only [ZMod.natCast_zmod_val] using ZMod.addOrderOf_coe y.val (NeZero.ne N)
  rw [ho,Nat.div_mul_cancel (Nat.gcd_dvd_left N y.val)]

/-- An actual axis relation with an odd seed forces the FULL binary
modulus bound in every dimension at least six. Thus no such axis corner
survives in the subbinary odd-seed G1 residual. -/
theorem two_pow_le_modulus_of_valid_two_chains_odd_seed_axis
    {A L u N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 6 ≤ A+L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hy : Odd y.val) (hu : 0 < u) (huL : u < 2^L) (hzero : u • y=0) :
    2^(A+L) ≤ N := by
  have ho := axis_relation_eq_addOrderOf_of_valid_two_chains hA hL (by omega)
    g hg x y hleft hright hu huL hzero
  obtain ⟨q,hq,hN⟩ := exists_odd_index_over_addOrderOf_of_odd_val y hy
  rw [← ho] at hN
  have hAp : 0 < 2^A := by positivity
  have hp := rectangle_card_bound_of_valid_two_chains hA hL (by omega)
    g hg x y hleft hright hAp huL (Or.inr hu.ne')
    (by simpa only [zero_nsmul,zero_add] using hzero)
  simp only [Nat.sub_zero,ZMod.card,pow_add] at hp
  have hdiff : u+(2^L-u)=2^L := Nat.add_sub_of_le huL.le
  have hqK : 2^A ≤ q := by nlinarith
  have hqmod := Nat.odd_iff.mp hq
  have hKmod := Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega : A ≠ 0))
  have hne : q ≠ 2^A := by
    intro he
    rw [he,hKmod] at hqmod
    omega
  have hqK' : 2^A+1 ≤ q := by omega
  have hs := small_corner_of_nonzero_relation_of_valid_two_chains hAp huL (Or.inr hu.ne')
    g hg x y hleft hright (by simpa only [zero_nsmul,zero_add] using hzero)
  simp only [Nat.sub_zero] at hs
  have hb : 2^L-u ≤ A+L+1-2^A := by omega
  have hmul := Nat.mul_le_mul_left (2^A+1) hb
  have hineq := two_chain_axis_corner_binary_inequality hA hL hn
  rw [pow_add]
  nlinarith

/-- Every small corner for a subbinary valid two-chain tuple with both
seeds odd is STRICTLY interior, in every dimension at least six. -/
theorem interior_corner_of_valid_odd_seed_subbinary_two_chains
    {A L a b N : ℕ} [NeZero N] (hA : 0 < A) (hL : 0 < L) (hn : 6 ≤ A+L)
    (g : Fin (A+L) → ZMod N) (hg : ValidTuple g) (x y : ZMod N)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : Odd x.val) (hy : Odd y.val) (hN : N < 2^(A+L))
    (ha0 : 0 < a) (ha : a ≤ 2^A) (hb0 : 0 < b) (hb : b ≤ 2^L) (hs : a+b ≤ A+L+1)
    (hzero : (2^A-a) • x+(2^L-b) • y=0) : a < 2^A ∧ b < 2^L := by
  have hw := two_chain_rectangle_wide_of_five_le (by omega : 5 ≤ A+L)
  constructor
  · by_contra hnot
    have he : a=2^A := by omega
    have hu : 0 < 2^L-b := by omega
    have huL : 2^L-b < 2^L := by omega
    have hz : (2^L-b) • y=0 := by simpa only [he,Nat.sub_self,zero_nsmul,zero_add] using hzero
    have hh := two_pow_le_modulus_of_valid_two_chains_odd_seed_axis hA hL hn
      g hg x y hleft hright hy hu huL hz
    omega
  · by_contra hnot
    have he : b=2^L := by omega
    have hu : 0 < 2^A-a := by omega
    let f : Fin (L+A) → ZMod N := fun i ↦ g (finAddFlip i)
    have hv : ValidTuple f := validTuple_embedding finAddFlip.toEmbedding g hg
    have hl : ∀ i : Fin L, f (Fin.castAdd A i)=2^i.val • y := by
      intro i
      simpa only [f,finAddFlip_apply_castAdd] using hright i
    have hr : ∀ i : Fin A, f (Fin.natAdd L i)=2^i.val • x := by
      intro i
      simpa only [f,finAddFlip_apply_natAdd] using hleft i
    have hz : (2^A-a) • x=0 := by simpa only [he,Nat.sub_self,zero_nsmul,add_zero] using hzero
    have hh := two_pow_le_modulus_of_valid_two_chains_odd_seed_axis hL hA (by omega)
      f hv y x hl hr hx hu (by omega : 2^A-a < 2^A) hz
    rw [Nat.add_comm L A] at hh
    omega

/-- The original critical two-escape G1 residual has a STRICTLY
INTERIOR odd-seed corner in every dimension at least six. Axis cases
are eliminated by actual cyclic order arithmetic, not discarded. -/
theorem exists_interior_odd_seed_corner_of_critical_two_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 5 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (B : Finset (Fin (n+1))) (hB : B.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    ∃ A L, 0 < A ∧ 0 < L ∧ A+L=n+1 ∧ ∃ E : Fin (A+L) ≃ Fin (n+1),
      ∃ x y : ZMod (2^(s+1)*q), Odd x.val ∧ Odd y.val ∧
      (∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x) ∧
      (∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y) ∧
      ∃ d u : ℕ, 0 < d ∧ d < 2^A ∧ 0 < u ∧ u < 2^L ∧
        d+u ≤ n+2 ∧ Even (d+u) ∧ 2^(n+1) ≤ 2^(s+1)*q+d*u ∧
        ((∃ e, d=2^e) ∨ ∃ f, u=2^f) ∧
        (2^A-d) • x+(2^L-u) • y=0 := by
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨A,L,hA,hL,hsize,E,x,y,hx,hy,hleft,hright,d,u,hd0,hdA,hu0,huL,hs,heven,hpay,hpow,hzero⟩ :=
    exists_odd_seed_corner_of_critical_two_escape_without_half hq (by omega)
      g hg hcritical B hB b hclosed hnohalf
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hbinary : 2^(s+1)*q < 2^(A+L) := by
    rw [hsize]
    exact lt_of_lt_of_le hcritical (Nat.sub_le _ _)
  obtain ⟨hdlt,hult⟩ := interior_corner_of_valid_odd_seed_subbinary_two_chains
    hA hL (by omega) _ hv x y hleft hright hx hy hbinary hd0 hdA hu0 huL (by omega) hzero
  exact ⟨A,L,hA,hL,hsize,E,x,y,hx,hy,hleft,hright,d,u,hd0,hdlt,hu0,hult,hs,heven,hpay,hpow,hzero⟩

end MinModulus
