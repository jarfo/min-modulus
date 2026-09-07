import MinModulus.TwoChainBoundary

/-! Complete G3 exclusion for two actual chains with equal doubled
endpoints, including a common value outside the tuple. The shallow
first weight pair always works; full depth uses cyclic calibration.
No arm order, depth, unit, odd calibration, or capacity input remains
in the final exceptional-modulus theorem. Global class lifting is next. -/

namespace MinModulus
open Finset

/-- Distinct terminal predecessors extract full discrepancy order even
when their common doubled value is OUTSIDE both chains. -/
theorem addOrderOf_equal_endpoint_discrepancy_of_valid
    {A L : ℕ} (hA : 0 < A) (hAL : A ≤ L)
    {G : Type*} [AddCommGroup G]
    (g : Fin (A+L) → G) (hg : ValidTuple g) (x y : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hjoin : 2^A • x=2^L • y) : addOrderOf (x-2^(L-A) • y)=2^A := by
  have hkill : 2^A • (x-2^(L-A) • y)=0 := by
    rw [smul_sub,smul_smul,← pow_add,show A+(L-A)=L by omega,hjoin,sub_self]
  have hnot : 2^(A-1) • (x-2^(L-A) • y) ≠ 0 := by
    intro hz
    rw [smul_sub,smul_smul,← pow_add,show A-1+(L-A)=L-1 by omega,sub_eq_zero] at hz
    let i : Fin A := ⟨A-1,by omega⟩
    let j : Fin L := ⟨L-1,by omega⟩
    have heq : g (Fin.castAdd L i)=g (Fin.natAdd A j) := by
      rw [hleft,hright]
      exact hz
    have he := congrArg Fin.val (validTuple_injective g hg heq)
    simp only [Fin.val_castAdd,Fin.val_natAdd,i,j] at he
    omega
  have hAform : A-1+1=A := by omega
  have h := addOrderOf_eq_prime_pow (p := 2) (n := A-1) hnot (by rwa [hAform])
  simpa only [hAform] using h

/-- For a common outside endpoint the shallow calibration's FIRST
weight pair always works: failure would require a three-entry tail
after the endpoint itself. No complementary fork-tail argument remains. -/
theorem not_validTuple_of_odd_calibrated_shallow_join
    {A L r : ℕ} (hA : 3 ≤ A) (hAL : A ≤ L)
    (hAr : A < r) (hrL : r ≤ L) (_hn : A+L < 2^r)
    {G : Type*} [AddCommGroup G]
    (g : Fin (A+L) → G) (x y z : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : x=2^(L-A) • y+z) (hkill : 2^A • z=0)
    (hcal : ∃ t : ℕ, t<2^A ∧ Odd t ∧ t • z=(2^L-2^(r-A)) • y) : ¬ ValidTuple g := by
  obtain ⟨t,htd,ht,hcal⟩ := hcal
  have htpos := ht.pos
  have hR : 2^(r-A) ≤ 2^(L-A) := Nat.pow_le_pow_right (by omega) (by omega)
  have hRL : 2^(r-A) ≤ 2^L := Nat.pow_le_pow_right (by omega) (by omega)
  have hv : 0 < 2^(L-A) := by positivity
  have hprod : 2^(L-A)*2^A=2^L := by rw [← pow_add,Nat.sub_add_cancel hAL]
  have hb : 2^(L-A)*(2^A-t)+2^(r-A)-1 < 2^L := by
    have hsum : 2^(L-A)*(2^A-t)+2^(L-A)*t=2^L := by
      rw [← Nat.mul_add,Nat.sub_add_cancel htd.le,hprod]
    have hmin : 2^(L-A) ≤ 2^(L-A)*t := by nlinarith
    omega
  have hhigh : A+L ≤ (t-1)+(2^(L-A)*(2^A-t)+2^(r-A)-1) := by
    by_contra h
    have htail := three_le_fork_tail_of_first_weights_too_small
      (B := L) hA hAL hAr htpos htd (show (t-1)+(2^(L-A)*(2^A-t)+2^(r-A)-1) < A+L by omega)
    omega
  have hid := calibrated_fork_two_weight_sum_identities
    (Nat.sub_add_cancel hRL) (by positivity : 0 < 2^(r-A)) htpos htd x y z hx hkill hcal
  exact not_validTuple_of_two_chain_small_integer_weights g x y hleft hright
    (by omega) hb hhigh (by omega) hid.1

/-- The calibrated full-depth rival also allows a common outside endpoint.
Only the predecessor entries need belong to the actual tuple. -/
theorem not_validTuple_of_calibrated_full_depth_join
    {A B L : ℕ} (hA : 0 < A) (hAB : A ≤ B) (hBL : B ≤ L) (hsize : A+L < 2^A)
    {G : Type*} [AddCommGroup G]
    (g : Fin (A+L) → G) (x y z : G)
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hx : x=2^(B-A) • y+z) (hkill : 2^A • z=0)
    (hcal : ∃ t : ℕ, t<2^A ∧ t • z=(2^L-1) • y) : ¬ ValidTuple g := by
  intro hg
  obtain ⟨t,ht,hcal⟩ := hcal
  by_cases ht0 : t=0
  · have hyzero : (2^L-1) • y=0 := by simpa only [ht0,zero_smul] using hcal.symm
    let f : Fin (L+A) → G := fun i ↦ g (finAddFlip i)
    have hf : ValidTuple f := validTuple_embedding finAddFlip.toEmbedding g hg
    have hfzero : (∑ i : Fin L, f (Fin.castAdd A i))=0 := by
      simp only [f,finAddFlip_apply_castAdd,hright]
      rw [← Finset.sum_smul,sum_binary_powers,hyzero]
    have hfchain : ∀ i : Fin A, f (Fin.natAdd L i)=2^i.val • x := by
      intro i
      simpa only [f,finAddFlip_apply_natAdd] using hleft i
    have hb := two_pow_chain_le_length_of_valid_zero_sum_fibre (by omega) f hf hfzero x hfchain
    omega
  · have htpos : 0 < t := by omega
    have hdpos : 0 < 2^A := by positivity
    have hvpos : 0 < 2^(B-A) := by positivity
    have hvd : 2^(B-A)*2^A=2^B := by rw [← pow_add,Nat.sub_add_cancel hAB]
    let X := t-1
    let Y := 2^(B-A)*(2^A-t)
    have hX : X < 2^A := by dsimp only [X]; omega
    have hY : Y < 2^L := by
      have hlt : Y < 2^B := by
        dsimp only [Y]
        rw [← hvd]
        exact Nat.mul_lt_mul_of_pos_left (by omega) hvpos
      have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : B ≤ L)
      omega
    have hhigh : A+L ≤ X+Y := by
      have hle : 2^A-t ≤ Y := by dsimp only [Y]; nlinarith
      dsimp only [X]
      omega
    have hneq : X ≠ 2^A-1 := by dsimp only [X]; omega
    have hcoef : X*2^(B-A)+Y=(2^A-1)*2^(B-A) := by
      dsimp only [X,Y]
      calc
        _=((t-1)+(2^A-t))*2^(B-A) := by ring
        _=_ := by congr 1; omega
    have htz : X • z+z=(2^L-1) • y := by
      rw [← succ_nsmul,show X+1=t by dsimp only [X]; omega,hcal]
    have hdz : (2^A-1) • z+z=0 := by
      rw [← succ_nsmul,Nat.sub_add_cancel (by omega : 1 ≤ 2^A),hkill]
    have hsum : X • x+Y • y=(2^A-1) • x+(2^L-1) • y := by
      have hleftsum : X • x+Y • y=((2^A-1)*2^(B-A)) • y+X • z := by
        rw [hx,smul_add,smul_smul]
        calc
          _=(X*2^(B-A)) • y+Y • y+X • z := by abel
          _=_ := by rw [← add_nsmul,hcoef]
      apply add_right_cancel (b := z)
      rw [hleftsum,hx,smul_add,smul_smul]
      calc
        _=((2^A-1)*2^(B-A)) • y+(X • z+z) := by abel
        _=((2^A-1)*2^(B-A)) • y+(2^L-1) • y := by rw [htz]
        _=((2^A-1)*2^(B-A)) • y+((2^A-1) • z+z)+(2^L-1) • y := by rw [hdz,add_zero]
        _=_ := by abel
    exact not_validTuple_of_two_chain_small_integer_weights g x y hleft hright hX hY hhigh hneq hsum hg

/-- Full-depth common-endpoint G3 arithmetic, with discrepancy order
and cyclic calibration both extracted from actual validity. -/
theorem not_validTuple_of_full_depth_equal_endpoint
    {A L : ℕ} (hA : 0 < A) (hAL : A ≤ L) (hsize : A+L < 2^A)
    (g : Fin (A+L) → ZMod ((2^L-1)*2^A))
    (x y : ZMod ((2^L-1)*2^A))
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hjoin : 2^A • x=2^L • y) : ¬ ValidTuple g := by
  intro hg
  have hM : 0 < 2^L-1 := by
    have hp : 2 ≤ 2^L := by simpa using Nat.pow_le_pow_right (by omega : 1 ≤ (2:ℕ)) (by omega : 1 ≤ L)
    omega
  letI : NeZero (2^A) := ⟨by positivity⟩
  letI : NeZero ((2^L-1)*2^A) := ⟨by positivity⟩
  let z := x-2^(L-A) • y
  have hz : addOrderOf z=2^A := addOrderOf_equal_endpoint_discrepancy_of_valid hA hAL g hg x y hleft hright hjoin
  have hkill : 2^A • z=0 := by simpa only [hz] using addOrderOf_nsmul_eq_zero z
  obtain ⟨t,ht,hcal⟩ := exists_bounded_coefficient_of_full_cyclic_kernel_order z y hz
  exact not_validTuple_of_calibrated_full_depth_join hA hAL le_rfl hsize g x y z
    hleft hright (by dsimp only [z]; abel) hkill ⟨t,ht,hcal⟩ hg

/-- Actual common-endpoint data extract order and odd calibration at
every shallow power-gap modulus; the first pair supplies the rival. -/
theorem not_validTuple_of_shallow_equal_endpoint_power_gap
    {A L r : ℕ} (hA : 3 ≤ A) (hAL : A ≤ L) (hrL : r ≤ L)
    (hAr : A < r) (hrn : r < A+L) (hn : A+L < 2^r)
    (g : Fin (A+L) → ZMod ((2^L-2^(r-A))*2^A))
    (x y : ZMod ((2^L-2^(r-A))*2^A))
    (hleft : ∀ i : Fin A, g (Fin.castAdd L i)=2^i.val • x)
    (hright : ∀ i : Fin L, g (Fin.natAdd A i)=2^i.val • y)
    (hmerge : 2^A • x=2^L • y) : ¬ ValidTuple g := by
  intro hg
  have hDpos : 0 < 2^L-2^(r-A) := by
    have hp := Nat.pow_lt_pow_right (by omega : 1 < (2 : ℕ)) (by omega : r-A < L)
    omega
  have hDsmall : 2^L-2^(r-A) < 2^L := by
    have hp : 0 < 2^(r-A) := by positivity
    omega
  have hDEven : Even (2^L-2^(r-A)) := by
    have hLform : L=L-1+1 := by omega
    have hrform : r-A=(r-A-1)+1 := by omega
    have hpL : 2^L=2*2^(L-1) := by conv_lhs => rw [hLform,pow_succ']
    have hpR : 2^(r-A)=2*2^(r-A-1) := by conv_lhs => rw [hrform,pow_succ']
    refine ⟨2^(L-1)-2^(r-A-1),?_⟩
    rw [hpL,hpR,← Nat.mul_sub_left_distrib]
    omega
  have hsubbinary : (2^L-2^(r-A))*2^A < 2^(A+L) := by
    calc
      _<2^L*2^A := Nat.mul_lt_mul_of_pos_right hDsmall (by positivity)
      _=2^(A+L) := by rw [← pow_add,Nat.add_comm]
  letI : NeZero (2^A) := ⟨by positivity⟩
  letI : NeZero ((2^L-2^(r-A))*2^A) := ⟨Nat.mul_ne_zero hDpos.ne' (NeZero.ne _)⟩
  let z := x-2^(L-A) • y
  have hz : addOrderOf z=2^A := addOrderOf_equal_endpoint_discrepancy_of_valid (by omega) hAL g hg x y hleft hright hmerge
  have hkill : 2^A • z=0 := by simpa only [hz] using addOrderOf_nsmul_eq_zero z
  obtain ⟨t,ht,hcal⟩ := exists_bounded_coefficient_of_full_cyclic_kernel_order z y hz
  have hx : x=2^(L-A) • y+z := by dsimp only [z]; abel
  have htodd := odd_fork_calibration_of_valid_subbinary_tuple (by omega : 0 < A) hDEven hsubbinary
    g hg x y z hleft hright hx hkill hcal
  exact not_validTuple_of_odd_calibrated_shallow_join hA hAL hAr hrL hn g x y z
    hleft hright hx hkill ⟨t,ht,htodd,hcal⟩ hg

/-- Affine actual common-endpoint data are excluded throughout both
the full-depth and shallow power-gap ranges. -/
theorem not_validTuple_of_affine_equal_endpoint_power_gap
    {A L r N : ℕ} (hA : 3 ≤ A) (hAL : A ≤ L) (hAr : A ≤ r) (hrL : r ≤ L)
    (hrn : r < A+L) (hn : A+L < 2^r)
    (hN : N=(2^L-2^(r-A))*2^A)
    (g : Fin (A+L) → ZMod N) (E : Equiv.Perm (Fin (A+L))) (b x y : ZMod N)
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hjoin : 2^A • x=2^L • y) : ¬ ValidTuple g := by
  subst N
  intro hg
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  rcases lt_or_eq_of_le hAr with hlt | heq
  · exact not_validTuple_of_shallow_equal_endpoint_power_gap hA hAL hrL hlt hrn hn
      _ x y hleft hright hjoin hv
  · subst r
    generalize hm : (2^L-2^(A-A))*2^A=M at *
    have hm' : M=(2^L-1)*2^A := by simpa only [Nat.sub_self,pow_zero] using hm.symm
    clear hm
    subst M
    exact not_validTuple_of_full_depth_equal_endpoint (by omega) hAL hn
      _ x y hleft hright hjoin hv

/-- COMPLETE exceptional exclusion for two chains with a common
outside endpoint. The shorter chain can have ANY depth; order,
calibration and all weight budgets are extracted. -/
theorem not_validTuple_exceptional_of_ordered_equal_endpoint_chains
    {A L : ℕ} (hA : 0 < A) (hAL : A ≤ L) (hn : 3 ≤ A+L)
    (hnpow : 2^Nat.log 2 (A+L) ≠ A+L)
    (g : Fin (A+L) → ZMod (2*globalBound (A+L-1)))
    (E : Equiv.Perm (Fin (A+L))) (b x y : ZMod (2*globalBound (A+L-1)))
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hjoin : 2^A • x=2^L • y) : ¬ ValidTuple g := by
  intro hg
  have hB : 2 ≤ globalBound (A+L-1) := (nmin_eq (by omega : 2 ≤ A+L-1)).1.1
  letI : NeZero (2*globalBound (A+L-1)) := ⟨by omega⟩
  by_cases hAsmall : A ≤ 2
  · have hshort : A+1 ≤ L := by
      by_contra h
      have hLA : L=A := by omega
      apply hnpow
      rw [hLA]
      rcases (show A=1 ∨ A=2 by omega) with rfl | rfl <;> decide
    have hb := global_lower_bound_of_valid_chain_with_at_most_two_extras hA hAsmall hshort
      g hg E b y hright
    have hnpow' : 2^Nat.log 2 ((A+L-1)+1) ≠ (A+L-1)+1 := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ A+L)] using hnpow
    have hgap : 2*globalBound (A+L-1) < globalBound (A+L) := by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ A+L)] using
        two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ A+L-1) hnpow'
    omega
  · let r := Nat.log 2 (A+L)+1
    have hdouble : ∀ t : ℕ, 3 ≤ t → 2*t < 2^t := by
      intro t ht
      induction t, ht using Nat.le_induction with
      | base => norm_num
      | succ t ht ih => rw [pow_succ']; omega
    have hnL : A+L < 2^L := by have h := hdouble L (by omega); omega
    have hrL : r ≤ L := by
      have h := Nat.log_lt_of_lt_pow (by omega : A+L ≠ 0) hnL
      dsimp only [r]
      omega
    have hrn : r < A+L := by omega
    have hnform : r+(A+L-r)=A+L := by omega
    have hfactor : 2*globalBound (A+L-1)=(2^(A+L-r)-1)*2^r := by
      have h := exceptional_modulus_eq_full_depth_fork_factor (A := r) (L := A+L-r)
        (by omega) (by rw [hnform]) (by simpa only [hnform] using hnpow)
      simpa only [hnform] using h
    have hq : Odd (2^(A+L-r)-1) := by
      have hp : 2^(A+L-r)=2*2^(A+L-r-1) := by
        have he : A+L-r=(A+L-r-1)+1 := by omega
        conv_lhs => rw [he,pow_succ']
      have hp0 : 0 < 2^(A+L-r-1) := by positivity
      exact ⟨2^(A+L-r-1)-1,by omega⟩
    have hv : ValidTuple (fun i ↦ g (E i)+b) := by
      simpa only [sub_neg_eq_add] using
        validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
    have hz := addOrderOf_equal_endpoint_discrepancy_of_valid hA hAL _ hv x y hleft hright hjoin
    have hAr : A ≤ r := dyadic_order_exponent_le_of_odd_factor
      (by rw [hfactor,Nat.mul_comm]) hq _ hz
    have hupper : A+L < 2^r := by
      have h := Nat.lt_pow_succ_log_self (by omega : 1 < (2:ℕ)) (A+L)
      simpa only [Nat.succ_eq_add_one] using h
    exact not_validTuple_of_affine_equal_endpoint_power_gap (by omega) hAL hAr hrL hrn hupper
      (exceptional_modulus_eq_fork_power_gap hn hAr rfl hnpow) g E b x y hleft hright hjoin hg

/-- Common-endpoint exceptional exclusion without an arm-ordering
input. The original affine/reindexed chains may be supplied either way. -/
theorem not_validTuple_of_equal_endpoint_chains_at_exceptional_modulus
    {A L N : ℕ} (hA : 0 < A) (hL : 0 < L) (hn : 3 ≤ A+L)
    (hnpow : 2^Nat.log 2 (A+L) ≠ A+L) (hN : N=2*globalBound (A+L-1))
    (g : Fin (A+L) → ZMod N) (E : Equiv.Perm (Fin (A+L))) (b x y : ZMod N)
    (hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x)
    (hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y)
    (hjoin : 2^A • x=2^L • y) : ¬ ValidTuple g := by
  by_cases hAL : A ≤ L
  · subst N
    exact not_validTuple_exceptional_of_ordered_equal_endpoint_chains hA hAL hn hnpow g E b x y hleft hright hjoin
  · intro hg
    let f : Fin (L+A) → ZMod N := fun i ↦ g (E (finAddFlip i))+b
    have hv : ValidTuple f := by
      simpa only [f,sub_neg_eq_add,Equiv.trans_apply] using
        validTuple_sub_const (fun i ↦ g ((finAddFlip.trans E) i))
          (validTuple_embedding (finAddFlip.trans E).toEmbedding g hg) (-b)
    have hN' : N=2*globalBound (L+A-1) := by simpa only [Nat.add_comm A L] using hN
    have hnpow' : 2^Nat.log 2 (L+A) ≠ L+A := by simpa only [Nat.add_comm A L] using hnpow
    clear hN
    subst N
    apply not_validTuple_exceptional_of_ordered_equal_endpoint_chains hL (by omega) (by omega) hnpow'
      f (Equiv.refl _) 0 y x ?_ ?_ hjoin.symm hv
    · intro i
      simpa only [Equiv.refl_apply,add_zero,f,finAddFlip_apply_castAdd] using hright i
    · intro i
      simpa only [Equiv.refl_apply,add_zero,f,finAddFlip_apply_natAdd] using hleft i

end MinModulus
