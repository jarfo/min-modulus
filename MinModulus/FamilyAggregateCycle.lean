import MinModulus.MaximalChainFamily

/-! Joint binary growth charges the incoming prefix and every surviving
chain to a single cycle replacement budget. At every depth t, with
B=2^t and D=t*B-(B-1), the total outside length K satisfies B*K<P+r*D,
where P is the extended covered length. Initial coverage S therefore
forces a majority cycle whenever B*n+2*r*D <= 2*(B-1)*S. Combined with
the existing continuation charge, this gives the original global,
every exact-stratum and G3 bounds for actual embedded families beyond
the separate-logarithm cutoffs. Unrestricted G1/G2/G3 remain open. -/

namespace MinModulus
open Finset
open scoped Classical

/-- A nonempty affine cycle and a disjoint actual chain family obey a
strict JOINT binary-growth budget, allowing empty family members and
arbitrary unselected coordinates. -/
theorem chain_family_weight_lt_of_disjoint_affine_cycle
    {β : Type*} [Fintype β] {n c : ℕ} (hc : 0 < c)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (b : G) (x : β → G) (L : β → ℕ)
    (e : Fin c ↪ Fin n) (f : (Σ a, Fin (L a)) ↪ Fin n) (R : Equiv.Perm (Fin c))
    (hdisj : ∀ i j, e i ≠ f j)
    (hcycle : ∀ i, g (e (R i))=2 • g (e i)+b)
    (hchain : ∀ a (i : Fin (L a)), g (f ⟨a,i⟩)+b=2^i.val • x a) :
    (∑ a, (2^(L a)-1)) < c+∑ a, L a := by
  classical
  let D := Σ a, Fin (L a)
  let k := Fintype.card D
  let Q : D ≃ Fin k := Fintype.equivFin D
  let A : Fin c ⊕ Fin k → Fin n := Sum.elim e (fun i ↦ f (Q.symm i))
  have hA : Function.Injective A := by
    rintro (i | i) (j | j) h
    · exact congrArg Sum.inl (e.injective h)
    · exact (hdisj i (Q.symm j) h).elim
    · exact (hdisj j (Q.symm i) h.symm).elim
    · exact congrArg Sum.inr (Q.symm.injective (f.injective h))
  let E : Fin (c+k) ↪ Fin n := ⟨fun i ↦ A (finSumFinEquiv.symm i),hA.comp finSumFinEquiv.symm.injective⟩
  have hleft (i : Fin c) : E (Fin.castAdd k i)=e i := by simp [E,A]
  have hright (i : Fin k) : E (Fin.natAdd c i)=f (Q.symm i) := by simp [E,A]
  let u : Fin (c+k) → G := fun i ↦ g (E i)+b
  have hu : ValidTuple u := by
    simpa only [u,sub_neg_eq_add] using validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E g hg) (-b)
  have hd : ∀ i, u (Fin.castAdd k (R i))=2 • u (Fin.castAdd k i) := by
    intro i
    simp only [u,hleft,hcycle,two_nsmul]
    abel
  have hzero : (∑ i : Fin c, u (Fin.castAdd k i))=0 :=
    sum_eq_zero_of_doubling_invariant R _ hd Finset.univ (by simp)
  let r : Fin k → ℕ := fun i ↦ (Q.symm i).2.val
  have hp : ∀ i, 0 < r i → ∃ j, r i=r j+1 ∧ u (Fin.natAdd c i)=2 • u (Fin.natAdd c j) := by
    intro i hi
    let a := (Q.symm i).1
    let t : Fin (L a) := (Q.symm i).2
    let j := Q ⟨a,⟨t.val-1,by have := t.isLt; change 0 < t.val at hi; omega⟩⟩
    have hqj : Q.symm j=⟨a,⟨t.val-1,by have := t.isLt; change 0 < t.val at hi; omega⟩⟩ := by simp [j]
    have hq : Q.symm i=⟨a,t⟩ := rfl
    refine ⟨j,?_,?_⟩
    · change (Q.symm i).2.val=(Q.symm j).2.val+1
      rw [hq,hqj]
      change t.val=t.val-1+1
      change 0 < t.val at hi
      omega
    · simp only [u,hright,hq,hqj,hchain]
      rw [← mul_smul,← pow_succ',Nat.sub_add_cancel (by change 0 < t.val at hi; omega)]
  have h := sum_two_pow_rank_lt_length_of_valid_zero_sum_fibre hc u hu hzero r hp
  have hweight : (∑ i : Fin k, 2^(r i))=∑ a, (2^(L a)-1) := by
    rw [← Q.sum_comp (fun i ↦ 2^(r i))]
    change (∑ z : D, 2^(Q.symm (Q z)).2.val)=_
    calc
      _ = ∑ z : D, 2^z.2.val := Finset.sum_congr rfl (fun z _ ↦
        congrArg (fun y : D ↦ (2 : ℕ)^y.2.val) (Q.symm_apply_apply z))
      _ = _ := by
        change (∑ z : Σ a, Fin (L a), 2^z.2.val)=_
        rw [Fintype.sum_sigma]
        exact Finset.sum_congr rfl (fun a _ ↦ sum_binary_powers (L a))
  have hk : k=∑ a, L a := by simp [k,D,Fintype.card_sigma]
  simpa only [hweight,hk] using h

/-- A binary chain has a uniform tangent bound at every integer depth.
This retains the combined lengths of short and long surviving arms. -/
theorem single_chain_binary_layer_lower_bound (L t : ℕ) :
    2^t*L ≤ (2^L-1)+(t*2^t-(2^t-1)) := by
  have hlevel : ∀ j, (Finset.univ.filter (fun i : Fin L ↦ i.val=j)).card ≤ 1 := by
    intro j
    apply Finset.card_le_one.mpr
    intro i hi k hk
    exact Fin.ext ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm)
  have h := two_pow_mul_card_le_rank_weight_add_layer_deficit (fun i : Fin L ↦ i.val) hlevel t
  simpa only [sum_binary_powers,sum_binary_layer_deficit,one_mul] using h

/-- Every member contributes to the same layer lower bound, with no
minimum length or nonempty-member assumption. -/
theorem chain_family_binary_layer_lower_bound
    {β : Type*} [Fintype β] (L : β → ℕ) (t : ℕ) :
    2^t*(∑ a, L a) ≤ (∑ a, (2^(L a)-1))+(Fintype.card β)*(t*2^t-(2^t-1)) := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ single_chain_binary_layer_lower_bound (L a) t)
  simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,← Finset.mul_sum] using h

/-- A strict joint growth budget gives an all-depth bound on the
TOTAL outside dimension, not separate logarithmic bounds per arm. -/
theorem chain_family_layer_budget_of_weight_lt
    {β : Type*} [Fintype β] (L : β → ℕ) {c : ℕ}
    (hweight : (∑ a, (2^(L a)-1)) < c+∑ a, L a) (t : ℕ) :
    2^t*(∑ a, L a) < c+(∑ a, L a)+(Fintype.card β)*(t*2^t-(2^t-1)) := by
  have h := chain_family_binary_layer_lower_bound L t
  omega

/-- The exact cycle suffix and all remaining family members satisfy
one joint layer budget at every depth. The incoming prefix is included
as a member; empty prefixes and arbitrary other coordinates are allowed. -/
theorem exists_cycle_with_joint_family_budget_of_rejoin
    {β : Type*} [Fintype β] [DecidableEq β] {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (b : G) (x : β → G)
    (M : β → ℕ) (V : β → ℕ → Fin n) (hMV : ActualAffineChainFamily g b x M V)
    (a : β) (j : ℕ) (hj : j < M a)
    (hjoin : g (V a j)=2 • g (V a (M a-1))+b) :
    ∃ c : ℕ, 0 < c ∧ c ≤ (∑ d, M d) ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), (∀ i, g (C (R i))=2 • g (C i)+b) ∧
        ∀ t : ℕ, 2^t*((∑ d, M d)-c) <
          (∑ d, M d)+(Fintype.card β)*(t*2^t-(2^t-1)) := by
  classical
  let c := M a-j
  have hc : 0 < c := by dsimp [c]; omega
  have hMa : j+c=M a := by dsimp [c]; omega
  let u : Fin (j+c) → G := fun i ↦ g (V a i.val)+b
  have hpow : ∀ i : Fin (j+c), u i=2^i.val • x a := by
    intro i
    exact hMV.1 a i.val (by have := i.isLt; omega)
  have hujoin : u (Fin.natAdd j ⟨0,hc⟩)=2 • u ⟨j+c-1,by omega⟩ := by
    change g (V a (j+0))+b=2 • (g (V a (j+c-1))+b)
    rw [Nat.add_zero,hMa,hjoin]
    simp only [two_nsmul]
    abel
  have hd := doubling_cycle_of_chain_suffix_rejoin hc u (x a) hpow hujoin
  let C : Fin c ↪ Fin n := ⟨fun i ↦ V a (j+i.val),by
    intro i k heq
    have hh := (hMV.2 a a (j+i.val) (j+k.val)
      (by have := i.isLt; omega) (by have := k.isLt; omega) heq).2
    apply Fin.ext
    omega⟩
  have hC : ∀ i, g (C (finRotate c i))=2 • g (C i)+b := by
    intro i
    have h := hd i
    change g (C (finRotate c i))+b=2 • (g (C i)+b) at h
    apply add_right_cancel (b := b)
    calc
      _=2 • (g (C i)+b) := h
      _=(2 • g (C i)+b)+b := by simp only [two_nsmul]; abel
  let L := Function.update M a j
  have hL : ∀ d, L d ≤ M d := by
    intro d
    by_cases hda : d=a
    · subst d; simp only [L,Function.update_self]; omega
    · simp [L,hda]
  let f : (Σ d, Fin (L d)) ↪ Fin n := ⟨fun z ↦ V z.1 z.2.val,by
    rintro ⟨d,i⟩ ⟨e,k⟩ heq
    obtain ⟨hde,hik⟩ := hMV.2 d e i.val k.val (i.isLt.trans_le (hL d)) (k.isLt.trans_le (hL e)) heq
    subst e
    have hi : i=k := Fin.ext hik
    subst k
    rfl⟩
  have hdisj : ∀ i z, C i ≠ f z := by
    intro i z heq
    rcases z with ⟨d,k⟩
    obtain ⟨had,hik⟩ := hMV.2 a d (j+i.val) k.val
      (by have := i.isLt; omega) (k.isLt.trans_le (hL d)) heq
    subst d
    have hk : k.val < j := by simpa [L] using k.isLt
    omega
  have hchain : ∀ d (i : Fin (L d)), g (f ⟨d,i⟩)+b=2^i.val • x d :=
    fun d i ↦ hMV.1 d i.val (i.isLt.trans_le (hL d))
  have hw := chain_family_weight_lt_of_disjoint_affine_cycle hc g hg b x L C f (finRotate c) hdisj hC hchain
  have hsum : c+(∑ d, L d)=∑ d, M d := by
    have hsplit := Finset.sum_erase_add Finset.univ M (Finset.mem_univ a)
    dsimp only [L]
    rw [Finset.sum_update_of_mem (Finset.mem_univ a),Finset.sdiff_singleton_eq_erase]
    omega
  have hcn : c ≤ ∑ d, M d := by omega
  refine ⟨c,hc,hcn,C,finRotate c,hC,?_⟩
  intro t
  have h := chain_family_layer_budget_of_weight_lt L hw t
  have hrem : (∑ d, M d)-c=∑ d, L d := by omega
  rw [hrem]
  simpa only [hsum] using h

/-- Joint binary growth turns an explicit all-depth coverage charge
into a majority cycle. The extended coverage may exceed the initial one. -/
theorem majority_of_joint_family_layer_budget
    {n S P c r t : ℕ} (hc : c ≤ P) (hS : S ≤ P)
    (hbudget : 2^t*(P-c) < P+r*(t*2^t-(2^t-1)))
    (hcover : 2^t*n+2*r*(t*2^t-(2^t-1)) ≤ 2*(2^t-1)*S) : n ≤ 2*c := by
  have hcover' := hcover.trans (Nat.mul_le_mul_left (2*(2^t-1)) hS)
  have hsplit := congrArg (fun z : ℕ ↦ 2^t*z) (Nat.sub_add_cancel hc)
  have hB : 1 ≤ (2 : ℕ)^t := Nat.one_le_two_pow
  have hdecomp : 2*(2^t-1)*P+2*P=2*2^t*P := by
    calc
      _=2*((2^t-1+1)*P) := by ring
      _=_ := by rw [Nat.sub_add_cancel hB]; ring
  by_contra hnot
  have hless : 2*c < n := by omega
  have hmul := Nat.mul_lt_mul_of_pos_left hless (by positivity : 0 < (2 : ℕ)^t)
  nlinarith

/-- The initial family's coverage is charged to collective growth of
ALL surviving chains, yielding an actual majority cycle at any chosen
depth. Endpoints and uncovered coordinates remain unrestricted. -/
theorem exists_majority_cycle_of_actual_family_layer_cover
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3)) (t : ℕ)
    (hcover : 2^t*n+2*(Fintype.card β)*(t*2^t-(2^t-1)) ≤ 2*(2^t-1)*(∑ i, L i)) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (C (R i))=2 • g (C i)+b := by
  obtain ⟨M,V,hMV,hgrow,hsize,i,hi,hjoin⟩ :=
    exists_actual_affine_chain_family_internal_rejoin g hg hsub b x L v hv a ha hcharge
  obtain ⟨c,hc,hcp,C,R,hC,hbudget⟩ := exists_cycle_with_joint_family_budget_of_rejoin
    g hg b x M V hMV a i hi hjoin
  have hmajor := majority_of_joint_family_layer_budget hcp hsize (hbudget t) hcover
  have hLa : L a ≤ n :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)).trans
      (actual_affine_chain_family_length_le g b x L v hv)
  exact ⟨c,by omega,hmajor,C,R,hC⟩

/-- Original global bound with collective, depth-parameterized coverage
for arbitrary embedded families of actual affine chains. -/
theorem global_lower_bound_of_affine_chain_family_layer_cover
    {β : Type*} [Fintype β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3)) (t : ℕ)
    (hcover : 2^t*n+2*(Fintype.card β)*(t*2^t-(2^t-1)) ≤ 2*(2^t-1)*(∑ i, L i)) :
    globalBound n ≤ N := by
  classical
  by_cases hsub : N < 2^n
  · have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
    obtain ⟨v,hv⟩ := exists_actual_affine_chain_family_of_embedding hn g b x L e hchain
    obtain ⟨c,hc,hmajor,C,R,hR⟩ := exists_majority_cycle_of_actual_family_layer_cover
      g hg hsub b x L v hv a ha hcharge t hcover
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact global_lower_bound_of_valid_majority_affine_doubling_cycle hc (by omega) g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Every original exact stratum at the same collective coverage bound. -/
theorem stratum_lower_bound_of_affine_chain_family_layer_cover
    {β : Type*} [Fintype β] {n s d : ℕ} (hd : Odd d)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g)
    (b : ZMod (2^s*d)) (x : β → ZMod (2^s*d)) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3)) (t : ℕ)
    (hcover : 2^t*n+2*(Fintype.card β)*(t*2^t-(2^t-1)) ≤ 2*(2^t-1)*(∑ i, L i)) :
    stratumBound n s ≤ 2^s*d := by
  classical
  letI : NeZero (2^s*d) := ⟨(mul_pos (by positivity) hd.pos).ne'⟩
  by_cases hsub : 2^s*d < 2^n
  · have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
    obtain ⟨v,hv⟩ := exists_actual_affine_chain_family_of_embedding hn g b x L e hchain
    obtain ⟨c,hc,hmajor,C,R,hR⟩ := exists_majority_cycle_of_actual_family_layer_cover
      g hg hsub b x L v hv a ha hcharge t hcover
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact stratum_lower_bound_of_valid_majority_affine_doubling_cycle hc (by omega) hd g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Original G3 exclusion with collective family coverage. -/
theorem not_validTuple_exceptional_of_affine_chain_family_layer_cover
    {β : Type*} [Fintype β] {n : ℕ} (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b : ZMod (2*globalBound (n-1))) (x : β → ZMod (2*globalBound (n-1))) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3)) (t : ℕ)
    (hcover : 2^t*n+2*(Fintype.card β)*(t*2^t-(2^t-1)) ≤ 2*(2^t-1)*(∑ i, L i)) :
    ¬ ValidTuple g := by
  intro hg
  have han : L a ≤ n := by
    have h := Fintype.card_le_of_injective (fun i : Fin (L a) ↦ e ⟨a,i⟩)
      (by intro i j h; have hh := e.injective h; cases hh; rfl)
    simpa only [Fintype.card_fin] using h
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have h := global_lower_bound_of_affine_chain_family_layer_cover g hg b x L e hchain a ha hcharge t hcover
  omega

end MinModulus
