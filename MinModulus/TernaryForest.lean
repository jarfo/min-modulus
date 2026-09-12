import MinModulus.TernarySegment
import MinModulus.ChainForestTrimmedPacking


/-!
# Parity-colored packing for arbitrary ternary forests

A same-parity collision in the seed coefficient box produces a balanced
ternary perturbation. Finite refinement preserves each arm's integer
profile, so validity forces a collision to meet one upper simplex. Its
stars-and-bars cardinality bounds the box by twice the ambient group size
plus a binomial term. The resulting exponential bound retains all arm
lengths and is extracted from actual injective acyclic affine tripling.
No conjectural induction hypothesis or finite cutoff is used.
-/

namespace MinModulus
open Finset

/-- Turning integral perturbations above minus one into a multiset
recovers the original sum plus the signed perturbation. -/
theorem sum_map_perturbed_replicates
    {α H : Type*} [Fintype α] [AddCommGroup H]
    (c : α → ℤ) (hc : ∀ i,-1 ≤ c i) (f : α → H) :
    ((∑ i,Multiset.replicate (1+c i).toNat i).map f).sum=
      (∑ i,f i)+(∑ i,c i • f i) := by
  have hp (i) : ((1+c i).toNat : ℤ)=1+c i :=
    Int.toNat_of_nonneg (by have := hc i; omega)
  have hh : ((∑ i,Multiset.replicate (1+c i).toNat i).map f).sum=
      ∑ i,(1+c i).toNat • f i :=
    (map_sum (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom f))
      (fun i ↦ Multiset.replicate (1+c i).toNat i) univ).trans (by simp)
  rw [hh]
  simp_rw [← natCast_zsmul,hp,add_zsmul,one_zsmul]
  rw [Finset.sum_add_distrib]

/-- A refinable balanced relation of the correct parity cannot change
any auxiliary additive profile when the original tuple is valid. -/
theorem ranked_ternary_relation_profile_eq_zero
    {n : ℕ} {G A : Type*} [AddCommGroup G] [AddCommGroup A]
    (g : Fin n → G) (hg : ValidTuple g) (rank : Fin n → ℕ) (w : Fin n → A)
    (hpred : ∀ i, 0 < rank i → ∃ j,
      rank i=rank j+1 ∧ g i=3 • g j ∧ w i=3 • w j)
    (c : Fin n → ℤ) (hc : ∀ i, -1 ≤ c i)
    (hs : (∑ i,c i) ≤ 0) (hpar : (∑ i,c i)%2=0)
    (hz : (∑ i,c i • g i)=0)
    (hweight : (n:ℤ) ≤ ∑ i,(1+c i)*(3:ℤ)^(rank i)) :
    (∑ i,c i • w i)=0 := by
  classical
  let p : Fin n → ℕ := fun i ↦ (1+c i).toNat
  have hp (i) : (p i : ℤ)=1+c i := Int.toNat_of_nonneg (by have := hc i; omega)
  let s : Multiset (Fin n) := ∑ i,Multiset.replicate (p i) i
  have hcard : s.card=∑ i,p i := by simp [s]
  have hcardInt : (s.card : ℤ)=n+∑ i,c i := by
    rw [hcard]
    push_cast
    simp_rw [hp]
    simp [Finset.sum_add_distrib]
  have hsum : (s.map (fun i ↦ (3:ℕ)^(rank i))).sum=∑ i,p i*(3:ℕ)^(rank i) := by
    exact (map_sum (Multiset.sumAddMonoidHom.comp
      (Multiset.mapAddMonoidHom (fun i : Fin n ↦ (3:ℕ)^(rank i))))
      (fun i ↦ Multiset.replicate (p i) i) univ).trans (by simp)
  have hsumInt : ((s.map (fun i ↦ (3:ℕ)^(rank i))).sum : ℤ)=
      ∑ i,(1+c i)*(3:ℤ)^(rank i) := by
    rw [hsum]
    push_cast
    simp_rw [hp]
  have hle : s.card ≤ n := by omega
  have hpar' : s.card%2=n%2 := by omega
  obtain ⟨r,hr⟩ : ∃ r,n=s.card+2*r := ⟨(n-s.card)/2,by omega⟩
  have hpred' : ∀ i, 0 < rank i → ∃ j,
      rank i=rank j+1 ∧ (g i,w i)=3 • (g j,w j) := by
    intro i hi
    obtain ⟨j,hj,hg,hw⟩ := hpred i hi
    exact ⟨j,hj,by simp only [hg,hw,Prod.smul_mk]⟩
  obtain ⟨t,ht,htx⟩ := exists_ranked_ternary_refinement rank
    (fun i ↦ (g i,w i)) hpred' s r (by omega)
  have hpair (u : Multiset (Fin n)) : (u.map (fun i ↦ (g i,w i))).sum=
      ((u.map g).sum,(u.map w).sum) := by
    induction u using Multiset.induction_on with
    | empty => rfl
    | cons i u ih => simp [ih]
  rw [hpair,hpair] at htx
  have hrepG : (s.map g).sum=(∑ i,g i)+(∑ i,c i • g i) :=
    sum_map_perturbed_replicates c hc g
  have hrepA : (s.map w).sum=(∑ i,w i)+(∑ i,c i • w i) :=
    sum_map_perturbed_replicates c hc w
  have hgroup : (t.map g).sum=∑ i,g i := by
    have hh := congrArg Prod.fst htx
    simpa only [hrepG,hz,add_zero] using hh
  have hall := multiset_count_eq_one_of_validTuple g hg t (by omega) hgroup
  have htotal : (t.map w).sum=∑ i,w i := by
    rw [Finset.sum_multiset_map_count]
    have hfull : t.toFinset=univ := Finset.eq_univ_of_forall (fun i ↦ by
      rw [Multiset.mem_toFinset,← Multiset.count_pos,hall]; omega)
    simp [hfull,hall]
  have hh := congrArg Prod.snd htx
  change (t.map w).sum=(s.map w).sum at hh
  rw [htotal,hrepA] at hh
  exact (add_left_cancel (show (∑ i,w i)+0=(∑ i,w i)+(∑ i,c i • w i) by simpa using hh)).symm

/-- In an actual ternary forest, a balanced relation whose coin budget
can be refined has zero integer displacement on every individual arm. -/
theorem balanced_ternary_forest_displacements_eq_zero
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)),g (E ⟨a,i⟩)+b=3^i.val • x a)
    (c : ∀ a,Fin (L a) → ℤ) (hc : ∀ a i,-1 ≤ c a i)
    (hs : (∑ a,∑ i,c a i) ≤ 0) (hpar : (∑ a,∑ i,c a i)%2=0)
    (hz : (∑ a,(∑ i,c a i*(3:ℤ)^i.val) • x a)=0)
    (hweight : (n:ℤ) ≤ ∑ a,∑ i,(1+c a i)*(3:ℤ)^i.val) :
    ∀ a,(∑ i,c a i*(3:ℤ)^i.val)=0 := by
  classical
  have hv : ValidTuple (fun i ↦ g i+b) := by
    simpa only [sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  let rank : Fin n → ℕ := fun i ↦ (E.symm i).2.val
  let coeff : Fin n → ℤ := fun i ↦ c (E.symm i).1 (E.symm i).2
  have hcoeffE (a) (i : Fin (L a)) : coeff (E ⟨a,i⟩)=c a i := by
    exact congrArg (fun p : Σ a : β,Fin (L a) ↦ c p.1 p.2) (E.symm_apply_apply ⟨a,i⟩)
  have hrankE (a) (i : Fin (L a)) : rank (E ⟨a,i⟩)=i.val := by
    exact congrArg (fun p : Σ a : β,Fin (L a) ↦ p.2.val) (E.symm_apply_apply ⟨a,i⟩)
  have hzi (f : Fin n → ℤ) : (∑ i,f i)=∑ a,∑ j : Fin (L a),f (E ⟨a,j⟩) := by
    rw [← E.sum_comp f,Fintype.sum_sigma]
  have hgi (f : Fin n → G) : (∑ i,f i)=∑ a,∑ j : Fin (L a),f (E ⟨a,j⟩) := by
    rw [← E.sum_comp f,Fintype.sum_sigma]
  have hcoeff : (∑ i,coeff i)=∑ a,∑ i,c a i := by
    rw [hzi]
    simp only [hcoeffE]
  have hzero : (∑ i,coeff i • (g i+b))=0 := by
    rw [hgi]
    simp only [hcoeffE,hchain]
    have hterm (a) (i : Fin (L a)) : c a i • (3^i.val • x a)=
        (c a i*(3:ℤ)^i.val) • x a := by
      rw [← natCast_zsmul,smul_smul]
      norm_cast
    simp_rw [hterm,← Finset.sum_smul]
    exact hz
  have hweight' : (n:ℤ) ≤ ∑ i,(1+coeff i)*(3:ℤ)^(rank i) := by
    rw [hzi]
    simpa only [hrankE,hcoeffE] using hweight
  intro a
  let w : Fin n → ℤ := fun i ↦ if a=(E.symm i).1 then (3:ℤ)^(rank i) else 0
  have hwE (a') (i : Fin (L a')) : w (E ⟨a',i⟩)=
      if a=a' then (3:ℤ)^i.val else 0 := by
    have hh := congrArg (fun p : Σ a : β,Fin (L a) ↦ p.1) (E.symm_apply_apply ⟨a',i⟩)
    simp only [w,hrankE,hh]
  have hpred : ∀ i,0 < rank i → ∃ j,
      rank i=rank j+1 ∧ g i+b=3 • (g j+b) ∧ w i=3 • w j := by
    intro i hi
    obtain ⟨⟨a',k⟩,rfl⟩ := E.surjective i
    have hk : 0 < k.val := by simpa only [hrankE] using hi
    let k' : Fin (L a') := ⟨k.val-1,by omega⟩
    have heq : k.val=k'.val+1 := by dsimp only [k']; omega
    refine ⟨E ⟨a',k'⟩,?_,?_,?_⟩
    · simpa only [hrankE] using heq
    · simp only [hchain,smul_smul]
      congr 1
      rw [heq,pow_succ]
      omega
    · simp only [hwE]
      by_cases hae : a=a'
      · simp only [if_pos hae]
        rw [heq,pow_succ]
        simp [mul_comm]
      · simp only [if_neg hae,smul_zero]
  have hh := ranked_ternary_relation_profile_eq_zero (fun i ↦ g i+b) hv rank w hpred
    coeff (fun i ↦ hc _ _) (by rwa [hcoeff]) (by rwa [hcoeff]) hzero hweight'
  have hprofile : (∑ i,coeff i • w i)=∑ i,c a i*(3:ℤ)^i.val := by
    rw [hzi]
    simp [hcoeffE,hwE]
  rwa [hprofile] at hh

/-- Every nontrivial ternary-box collision of the same parity has
one orientation whose full integer coin budget is below the tuple length. -/
theorem ternary_box_collision_joint_distance_lt
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)),g (E ⟨a,i⟩)+b=3^i.val • x a)
    (p q : β → ℕ)
    (hp : ∀ a,p a ≤ ∑ i : Fin (L a),(3:ℕ)^i.val)
    (hq : ∀ a,q a ≤ ∑ i : Fin (L a),(3:ℕ)^i.val)
    (hne : p ≠ q) (heq : (∑ a,p a • x a)=∑ a,q a • x a)
    (hpar : (∑ a,p a)%2=(∑ a,q a)%2) :
    (∑ a,((∑ i : Fin (L a),(3:ℕ)^i.val)-p a))+(∑ a,q a) < n ∨
      (∑ a,((∑ i : Fin (L a),(3:ℕ)^i.val)-q a))+(∑ a,p a) < n := by
  classical
  let M : β → ℕ := fun a ↦ ∑ i : Fin (L a),(3:ℕ)^i.val
  have hcast (a) : (M a : ℤ)=∑ i : Fin (L a),(3:ℤ)^i.val := by
    simp only [M,Nat.cast_sum,Nat.cast_pow,Nat.cast_ofNat]
  have hbalanced (a) : ∃ c : Fin (L a) → ℤ,
      (∀ i,-1 ≤ c i ∧ c i ≤ 1) ∧ (∑ i,c i*(3:ℤ)^i.val)=(p a:ℤ)-q a := by
    apply exists_balanced_ternary_coefficients
    rw [abs_le,← hcast]
    have hpa : p a ≤ M a := hp a
    have hqa : q a ≤ M a := hq a
    constructor <;> omega
  choose c hc he using hbalanced
  have heven : (∑ a,∑ i,c a i)%2=0 := by
    have hm : (∑ a,∑ i,c a i*(3:ℤ)^i.val) ≡ (∑ a,∑ i,c a i) [ZMOD 2] := by
      apply Int.ModEq.sum
      intro a _
      apply Int.ModEq.sum
      intro i _
      simpa using (Int.ModEq.refl (c a i)).mul ((show (3:ℤ) ≡ 1 [ZMOD 2] by decide).pow i.val)
    change _%2=_%2 at hm
    simp only [he,Finset.sum_sub_distrib,← Nat.cast_sum] at hm
    omega
  have hzero : (∑ a,(∑ i,c a i*(3:ℤ)^i.val) • x a)=0 := by
    simp only [he,sub_smul,natCast_zsmul,Finset.sum_sub_distrib,heq,sub_self]
  have hplus : (∑ a,∑ i,(1+c a i)*(3:ℤ)^i.val)=
      ((∑ a,(M a-q a))+(∑ a,p a) : ℕ) := by
    have hpoint (a) : (∑ i,(1+c a i)*(3:ℤ)^i.val)=((M a-q a+p a : ℕ):ℤ) := by
      simp only [add_mul,one_mul,Finset.sum_add_distrib,he,← hcast]
      have hqa : q a ≤ M a := hq a
      omega
    simp only [hpoint,← Nat.cast_sum,Finset.sum_add_distrib]
  have hminus : (∑ a,∑ i,(1+(-c a i))*(3:ℤ)^i.val)=
      ((∑ a,(M a-p a))+(∑ a,q a) : ℕ) := by
    have hpoint (a) : (∑ i,(1+(-c a i))*(3:ℤ)^i.val)=((M a-p a+q a : ℕ):ℤ) := by
      simp only [add_mul,one_mul,Finset.sum_add_distrib,neg_mul,Finset.sum_neg_distrib,he,← hcast]
      have hpa : p a ≤ M a := hp a
      omega
    simp only [hpoint,← Nat.cast_sum,Finset.sum_add_distrib]
  by_contra hnot
  have hlo : n ≤ (∑ a,(M a-p a))+(∑ a,q a) := by
    exact Nat.le_of_not_gt (fun h ↦ hnot (Or.inl h))
  have hhi : n ≤ (∑ a,(M a-q a))+(∑ a,p a) := by
    exact Nat.le_of_not_gt (fun h ↦ hnot (Or.inr h))
  by_cases hs : (∑ a,∑ i,c a i) ≤ 0
  · have hall := balanced_ternary_forest_displacements_eq_zero L g hg E x b hchain c
      (fun a i ↦ (hc a i).1) hs heven hzero (by rw [hplus]; exact_mod_cast hhi)
    apply hne
    funext a
    have hh := hall a
    rw [he] at hh
    omega
  · have hneg : (∑ a,∑ i,-c a i)= -(∑ a,∑ i,c a i) := by
      simp only [Finset.sum_neg_distrib]
    have hall := balanced_ternary_forest_displacements_eq_zero L g hg E x b hchain
      (fun a i ↦ -c a i) (fun a i ↦ by have := (hc a i).2; omega)
      (by rw [hneg]; omega) (by rw [hneg]; omega)
      (by simpa only [neg_mul,Finset.sum_neg_distrib,neg_smul,neg_eq_zero] using hzero)
      (by rw [hminus]; exact_mod_cast hlo)
    apply hne
    funext a
    have hh := hall a
    simp only [neg_mul,Finset.sum_neg_distrib,he] at hh
    omega

/-- A same-parity collision in the ternary box must meet the upper simplex. -/
theorem ternary_box_collision_meets_upper_simplex
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)),g (E ⟨a,i⟩)+b=3^i.val • x a)
    (p q : β → ℕ)
    (hp : ∀ a,p a ≤ ∑ i : Fin (L a),(3:ℕ)^i.val)
    (hq : ∀ a,q a ≤ ∑ i : Fin (L a),(3:ℕ)^i.val)
    (hne : p ≠ q) (heq : (∑ a,p a • x a)=∑ a,q a • x a)
    (hpar : (∑ a,p a)%2=(∑ a,q a)%2) :
    (∑ a,((∑ i : Fin (L a),(3:ℕ)^i.val)-p a)) < n ∨
      (∑ a,((∑ i : Fin (L a),(3:ℕ)^i.val)-q a)) < n := by
  exact (ternary_box_collision_joint_distance_lt L g hg E x b hchain p q hp hq hne heq hpar).imp
    (fun h ↦ by omega) (fun h ↦ by omega)

/-- One upper simplex accounts for every collision in the parity-colored
ternary box of an arbitrary actual forest. -/
theorem ternary_forest_box_card_bound
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)),g (E ⟨a,i⟩)+b=3^i.val • x a) :
    (∏ a,((∑ i : Fin (L a),(3:ℕ)^i.val)+1)) ≤
      2*Fintype.card G+(n+Fintype.card β-1).choose (Fintype.card β) := by
  classical
  let M : β → ℕ := fun a ↦ ∑ i : Fin (L a),(3:ℕ)^i.val
  let B := ∀ a,Fin (M a+1)
  let C : B → Prop := fun p ↦ (∑ a,(M a-(p a).val)) < n
  let R := {p : B // ¬ C p}
  let f : R → G × Fin 2 := fun p ↦
    (∑ a,(p.val a).val • x a,⟨(∑ a,(p.val a).val)%2,Nat.mod_lt _ (by decide)⟩)
  have hbox : Fintype.card B=∏ a,(M a+1) := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
  let dist : {p : B // C p} → β → ℕ := fun p a ↦ M a-(p.val a).val
  have hdist : Function.Injective dist := by
    intro p q he
    apply Subtype.ext
    funext a
    apply Fin.ext
    have hh : M a-(p.val a).val=M a-(q.val a).val := congrFun he a
    have := (p.val a).isLt
    have := (q.val a).isLt
    omega
  have hcorner := card_le_choose_of_injective_small_sum_profiles hn dist hdist (fun p ↦ p.property)
  have hR : Fintype.card R=(∏ a,(M a+1))-Fintype.card {p : B // C p} := by
    change Fintype.card {p : B // ¬ C p}=_
    rw [Fintype.card_subtype_compl C,hbox]
  have hi : Function.Injective f := by
    intro p q he
    by_contra hne
    have hvalues : (fun a ↦ (p.val a).val) ≠ (fun a ↦ (q.val a).val) := by
      intro h
      apply hne
      apply Subtype.ext
      funext a
      exact Fin.ext (congrFun h a)
    have hvalue : (∑ a,(p.val a).val • x a)=∑ a,(q.val a).val • x a :=
      congrArg Prod.fst he
    have hpar : (∑ a,(p.val a).val)%2=(∑ a,(q.val a).val)%2 :=
      congrArg (fun z : G × Fin 2 ↦ z.2.val) he
    rcases ternary_box_collision_meets_upper_simplex L g hg E x b hchain
        (fun a ↦ (p.val a).val) (fun a ↦ (q.val a).val)
        (fun a ↦ by have := (p.val a).isLt; change (p.val a).val ≤ M a; omega)
        (fun a ↦ by have := (q.val a).isLt; change (q.val a).val ≤ M a; omega)
        hvalues hvalue hpar with hp | hq
    · exact p.property hp
    · exact q.property hq
  have hh := Fintype.card_le_of_injective f hi
  rw [hR] at hh
  simp only [Fintype.card_prod,Fintype.card_fin] at hh
  have hcorner_le : Fintype.card {p : B // C p} ≤ ∏ a,(M a+1) := by
    rw [← hbox]
    exact Fintype.card_subtype_le C
  change (∏ a,(M a+1)) ≤ _
  omega

/-- The actual ternary forest gives exponential growth after paying
one parity factor and one binary factor per arm, plus a binomial corner. -/
theorem ternary_forest_exponential_card_bound
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)),g (E ⟨a,i⟩)+b=3^i.val • x a) :
    3^n ≤ 2^(Fintype.card β+1)*Fintype.card G+
      2^(Fintype.card β)*(n+Fintype.card β-1).choose (Fintype.card β) := by
  have hsize : (∑ a,L a)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hpoint (a) : 3^(L a) ≤ 2*((∑ i : Fin (L a),(3:ℕ)^i.val)+1) := by
    have hh := two_mul_sum_ternary_powers_add_one (L a)
    omega
  have hv : (∏ a,(3:ℕ)^(L a)) ≤ ∏ a,2*((∑ i : Fin (L a),(3:ℕ)^i.val)+1) :=
    Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun a _ ↦ hpoint a)
  rw [Finset.prod_pow_eq_pow_sum,hsize] at hv
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hv
  have hb := ternary_forest_box_card_bound hn L g hg E x b hchain
  calc
    3^n ≤ 2^(Fintype.card β)*(∏ a,((∑ i : Fin (L a),(3:ℕ)^i.val)+1)) := hv
    _ ≤ 2^(Fintype.card β)*(2*Fintype.card G+
        (n+Fintype.card β-1).choose (Fintype.card β)) := Nat.mul_le_mul_left _ hb
    _ = _ := by rw [pow_succ]; ring

/-- An ordered sequence of actual tripling arrows is a ternary segment. -/
theorem powers_of_ordered_tripling_arrows
    {L : ℕ} (hL : 0 < L) {G : Type*} [AddCommGroup G]
    (y : Fin L → G)
    (harrow : ∀ (i : Fin L) (hi : i.val+1 < L),y ⟨i.val+1,hi⟩=3 • y i) :
    ∀ i,y i=3^i.val • y ⟨0,hL⟩ := by
  cases L with
  | zero => omega
  | succ L =>
    intro i
    induction i using Fin.induction with
    | zero => simp
    | succ i ih =>
      have hh := harrow i.castSucc (by simp)
      change y i.succ=3 • y i.castSucc at hh
      rw [hh,ih]
      simp [Fin.val_succ,pow_succ,smul_smul,Nat.mul_comm]

/-- Actual injective acyclic affine tripling outside a marked escape set
produces complete ternary chains, retaining every coordinate and endpoint. -/
theorem exists_ternary_forest_of_injective_acyclic_affine_tripling
    {α : Type*} [Fintype α] {G : Type*} [AddCommGroup G]
    (g : α → G) (hinj : Function.Injective (fun i ↦ 3 • g i))
    (A : Finset α) (b : G) (hclosed : ∀ i,i ∉ A → ∃ j,g j=3 • g i+2 • b)
    (hacyclic : ∀ {m : ℕ},0 < m → ∀ e : Fin m ↪ α,∀ P : Equiv.Perm (Fin m),
      ¬ (∀ i,g (e (P i))=3 • g (e i)+2 • b)) :
    ∃ L : A → ℕ,(∀ a,0 < L a) ∧ (∑ a,L a)=Fintype.card α ∧
      ∃ E : (Σ a : A,Fin (L a)) ≃ α,∃ x : A → G,
      (∀ a (i : Fin (L a)),g (E ⟨a,i⟩)+b=3^i.val • x a) ∧
      (∀ a (i : Fin (L a)),i.val+1=L a → E ⟨a,i⟩=a.val) := by
  classical
  let R : α → α := fun i ↦ if hi : i ∈ A then i else Classical.choose (hclosed i hi)
  have hfix : ∀ i,i ∈ A → R i=i := by intro i hi; simp only [R,dif_pos hi]
  have hd : ∀ i,i ∉ A → g (R i)=3 • g i+2 • b := by
    intro i hi
    simpa only [R,dif_neg hi] using Classical.choose_spec (hclosed i hi)
  have hRi : ∀ i,i ∉ A → ∀ j,j ∉ A → R i=R j → i=j := by
    intro i hi j hj he
    apply hinj
    apply add_right_cancel (b := 2 • b)
    rw [← hd i hi,← hd j hj,he]
  rcases rank_or_nonempty_cycle_avoiding_set R (↑A : Set α) with ⟨r,hz,hr⟩ | ⟨m,hm,e,P,he,hP⟩
  · obtain ⟨L,hL,E,hEr,hEa,hEe⟩ := exists_full_chain_forest_of_ranked_injective_map R A hfix r hz hr hRi
    have hcard : (∑ a,L a)=Fintype.card α := by
      simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
    let x : A → G := fun a ↦ g (E ⟨a,⟨0,hL a⟩⟩)+b
    refine ⟨L,hL,hcard,E,x,?_,hEe⟩
    intro a
    apply powers_of_ordered_tripling_arrows (hL a)
    intro i hi
    have hnot : E ⟨a,i⟩ ∉ A := by
      intro h
      have h0 := (hz _).mpr h
      have hh := hEr a i
      omega
    rw [← hEa a i hi,hd _ hnot]
    simp only [three_nsmul,two_nsmul]
    abel
  · exact (hacyclic hm e P (by intro i; rw [hP,hd _ (he i)])).elim

/-- The exponential bound is extracted from the actual affine tripling
map, with no supplied forest or chain-length normal form. -/
theorem exponential_bound_of_injective_acyclic_affine_tripling
    {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hinj : Function.Injective (fun i ↦ 3 • g i))
    (A : Finset (Fin n)) (b : G) (hclosed : ∀ i,i ∉ A → ∃ j,g j=3 • g i+2 • b)
    (hacyclic : ∀ {m : ℕ},0 < m → ∀ e : Fin m ↪ Fin n,∀ P : Equiv.Perm (Fin m),
      ¬ (∀ i,g (e (P i))=3 • g (e i)+2 • b)) :
    3^n ≤ 2^(A.card+1)*Fintype.card G+2^A.card*(n+A.card-1).choose A.card := by
  obtain ⟨L,_,_,E,x,hchain,_⟩ :=
    exists_ternary_forest_of_injective_acyclic_affine_tripling g hinj A b hclosed hacyclic
  simpa only [Fintype.card_coe] using
    ternary_forest_exponential_card_bound hn L g hg E x b hchain

end MinModulus
