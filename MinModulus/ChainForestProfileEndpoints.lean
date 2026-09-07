import MinModulus.ChainForestProfileSparseSides

/-! Genuine escaping boundaries avoid nonzero small points on other box
faces under joint forest capacity. In three chains this orders a
no-overflow profile below a compatible strip and classifies equality.
The unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- Twice one actual entry cannot be the sum of two distinct actual
entries: replacing that pair gives a length-preserving rival. -/
theorem two_nsmul_ne_sum_distinct_of_validTuple
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (a b c : Fin n) (hab : a ≠ b) :
    2 • g c ≠ g a+g b := by
  classical
  intro he
  let w : Fin n → ℤ := fun i ↦ (if i=c then 2 else 0)-(if i=a then 1 else 0)-(if i=b then 1 else 0)
  apply (validTuple_iff_no_zero_witness g).mp hg w
  refine ⟨?_,?_,?_,?_⟩
  · intro hw
    have hh := congrFun hw c
    simp only [w,if_true,Pi.zero_apply] at hh
    split_ifs at hh <;> omega
  · intro i
    dsimp only [w]
    split_ifs <;> omega
  · simp [w,Finset.sum_sub_distrib]
  · simp only [w,sub_smul,ite_smul,zero_smul,one_smul,Finset.sum_sub_distrib,
      Finset.sum_ite_eq',Finset.mem_univ,if_true,two_zsmul]
    simp only [two_nsmul] at he
    rw [show g c+g c-g a-g b=(g c+g c)-(g a+g b) by abel,he,sub_self]

/-- Genuine forest boundaries cannot equal any single entry on another
chain, or a sum of two distinct entries on that chain. -/
theorem genuine_forest_boundary_not_one_or_two_powers
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (a j : β) :
    (∀ p, p < L j → 2^(L a) • x a ≠ 2^p • x j) ∧
      ∀ p q, p < L j → q < L j → p ≠ q →
        2^(L a) • x a ≠ (2^p+2^q) • x j := by
  classical
  let last : Fin n := E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩
  have hend : 2^(L a) • x a=2 • (g last+b) := by
    rw [hchain a ⟨L a-1,by have := hL a; omega⟩,smul_smul]
    have hpow : 2^(L a)=2*2^(L a-1) := by
      rw [← pow_succ']
      congr 1
      have := hL a
      omega
    exact congrArg (fun r : ℕ ↦ r • x a) hpow
  constructor
  · intro p hp he
    have hc := hchain j ⟨p,hp⟩
    have hh : g (E ⟨j,⟨p,hp⟩⟩)=2 • g last+b := by
      rw [hend] at he
      rw [← hc] at he
      apply add_right_cancel (b := b)
      calc
        _ = 2 • (g last+b) := he.symm
        _ = _ := by simp only [two_nsmul]; abel
    exact hgen a _ hh
  · intro p q hp hq hpq he
    have hneq : E ⟨j,⟨p,hp⟩⟩ ≠ E ⟨j,⟨q,hq⟩⟩ := by
      intro hh
      have hfin := E.injective hh
      cases hfin
      exact hpq rfl
    have hh : 2 • g last=g (E ⟨j,⟨p,hp⟩⟩)+g (E ⟨j,⟨q,hq⟩⟩) := by
      rw [hend,add_nsmul,← hchain j ⟨p,hp⟩,← hchain j ⟨q,hq⟩] at he
      apply add_right_cancel (b := b+b)
      calc
        _ = 2 • (g last+b) := by simp only [two_nsmul]; abel
        _ = _ := he
        _ = _ := by abel
    exact two_nsmul_ne_sum_distinct_of_validTuple g hg _ _ last hneq hh

/-- An axis profile and a strip profile force an actual short-chain
boundary equal to their signed dominant-height difference. -/
theorem axis_profile_strip_boundary_relation
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (x : β → G)
    (j a : β) (haj : a ≠ j)
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (ha : (w a).val=2^(L a)) (hwz : ∀ i, i ≠ j → i ≠ a → (w i).val=0)
    (hvz : ∀ i, i ≠ j → (v i).val=0) :
    2^(L a) • x a+((w j).val+1) • x j=((v j).val+1) • x j := by
  classical
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hws : (∑ i, (w i).val • x i)=(w j).val • x j+2^(L a) • x a := by
    calc
      _ = ∑ i, ((if i=j then (w j).val • x j else 0)+(if i=a then 2^(L a) • x a else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i=j
        · subst i; simp [Ne.symm haj]
        · by_cases hia : i=a
          · subst i; simp [haj,ha]
          · simp [hij,hia,hwz i hij hia]
      _ = _ := by simp [Finset.sum_add_distrib]
  have hvs : (∑ i, (v i).val • x i)=(v j).val • x j := by
    apply Finset.sum_eq_single j
    · intro i _ hij; rw [hvz i hij,zero_nsmul]
    · simp
  have he : (w j).val • x j+2^(L a) • x a=(v j).val • x j := hws.symm.trans (hwm.2.trans (hvm.2.symm.trans hvs))
  simp only [add_nsmul,one_nsmul]
  calc
    _=((w j).val • x j+2^(L a) • x a)+x j := by abel
    _=_ := congrArg (fun z ↦ z+x j) he

/-- A genuine escaping boundary cannot equal ANY positive weight below
n on another axis when the forest box is wide. Nonpowers save the two
coins needed to add the short boundary; binary refinement restores the
full tuple length. No lower bound on the short arm is imposed. -/
theorem genuine_forest_boundary_not_small_axis_weight
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (a j : β) (haj : a ≠ j) (c : ℕ) (hc0 : 0 < c) (hcn : c < n) (hcK : c < 2^(L j)) :
    2^(L a) • x a ≠ c • x j := by
  classical
  intro he
  by_cases hp : ∃ p, c=2^p
  · obtain ⟨p,hp⟩ := hp
    have hpj : p < L j := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by omega)
    exact (genuine_forest_boundary_not_one_or_two_powers L hL g hg E x b hchain hgen a j).1 p hpj (by rw [← hp]; exact he)
  · have hLj : 2 ≤ L j := by
      by_contra hn
      have hLj1 : L j=1 := by have := hL j; omega
      have hc1 : c=1 := by rw [hLj1,pow_one] at hcK; omega
      exact hp ⟨0,by simp [hc1]⟩
    let X : β → ℕ := fun i ↦ if i=j then 2^(L i)-1-c else if i=a then 2*(2^(L i))-1 else 2^(L i)-1
    have hrep : ∀ i, ∃ u, val (L i) u=X i ∧
        dsum (L i) u+(if i=j then 2 else 0) ≤ L i+(if i=a then 2 else 0) := by
      intro i
      by_cases hij : i=j
      · subst i
        obtain ⟨u,_,hu,hcost⟩ := exists_rep_compl (L j) c hcK hc0.ne' hp
        refine ⟨u,?_,?_⟩
        · simpa only [X,if_true] using hu
        · simp only [if_true,if_neg (Ne.symm haj),add_zero]; omega
      · by_cases hia : i=a
        · subst i
          obtain ⟨u,hu,hv,hcost⟩ := exists_rep_le (L a) (2^(L a)-1) (by have := Nat.two_pow_pos (L a); omega)
          obtain ⟨v,_,hv',hc'⟩ := exists_binary_rep_add_two_top_coins (hL a) u hu
          refine ⟨v,?_,?_⟩
          · rw [hv',hv]; simp only [X,if_neg haj,if_true]; have := Nat.two_pow_pos (L a); omega
          · simp only [if_neg haj,if_true,add_zero]; omega
        · obtain ⟨u,_,hu,hcost⟩ := exists_rep_le (L i) (2^(L i)-1) (by have := Nat.two_pow_pos (L i); omega)
          exact ⟨u,by simpa only [X,if_neg hij,if_neg hia] using hu,
            by simpa only [if_neg hij,if_neg hia,add_zero] using hcost⟩
    choose u hu hc using hrep
    have hsize : (∑ i, L i)=n := by
      simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
    have hcost : (∑ i, dsum (L i) (u i)) ≤ n := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hc i)
      simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,hsize] at hh
      omega
    have hpoint : ∀ i, X i+(if i=j then c else 0)=(2^(L i)-1)+(if i=a then 2^(L a) else 0) := by
      intro i
      by_cases hij : i=j
      · subst i; simp only [X,if_true,if_neg (Ne.symm haj),add_zero]; omega
      · by_cases hia : i=a
        · subst i; simp only [X,if_neg haj,if_true,add_zero]; have := Nat.two_pow_pos (L a); omega
        · simp only [X,if_neg hij,if_neg hia,add_zero]
    have hweights : (∑ i, X i)+c=(∑ i, (2^(L i)-1))+2^(L a) := by
      have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ ↦ hpoint i)
      simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh
    have hsum : (∑ i, X i • x i)=∑ i, (2^(L i)-1) • x i := by
      have hh : (∑ i, X i • x i)+c • x j=(∑ i, (2^(L i)-1) • x i)+2^(L a) • x a := by
        calc
          _=∑ i, (X i+(if i=j then c else 0)) • x i := by simp [add_nsmul,ite_smul,Finset.sum_add_distrib]
          _=∑ i, ((2^(L i)-1)+(if i=a then 2^(L a) else 0)) • x i := by simp only [hpoint]
          _=_ := by simp [add_nsmul,ite_smul,Finset.sum_add_distrib]
      rw [he] at hh
      exact add_right_cancel hh
    exact not_validTuple_of_chain_forest_integer_weights L X g E x b hchain u hu hcost
      (by have := Nat.two_pow_pos (L a); omega) ⟨j,by simp only [X,if_true]; omega⟩ hsum hg

/-- A no-overflow profile concentrated on the dominant axis cannot sit
higher than a coexisting compatible strip. Any positive height difference
would identify the short escaping boundary with a forbidden small axis
weight. -/
theorem axis_profile_height_le_compatible_strip_height
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : n ≤ 2^(L j))
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val)
    (hvz : ∀ i, i ≠ j → (v i).val=0) : (v j).val+1 ≤ (w j).val+1 := by
  classical
  by_contra hn
  obtain ⟨haj,hwa,hwz,_,_,_⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j hwidth w hw hcompat a ha
  have he := axis_profile_strip_boundary_relation L x j a haj w v hw hv hwa hwz hvz
  have hboundary : 2^(L a) • x a=((v j).val-(w j).val) • x j := by
    apply add_right_cancel (b := ((w j).val+1) • x j)
    rw [he,← add_nsmul]
    congr 1
    omega
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hsingle := Finset.single_le_sum (f := fun i ↦ (v i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
  exact genuine_forest_boundary_not_small_axis_weight L hL hwide g hg E x b hchain hgen
    a j haj ((v j).val-(w j).val) (by omega) (by omega) (by omega) hboundary

/-- Two compatible strips on the two companion arms force any coexisting
no-overflow profile onto the dominant axis. Genuine endpoints then put
its height below BOTH strip heights. All three profiles are actual. -/
theorem two_compatible_strips_force_lower_axis_profile
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : n ≤ 2^(L j))
    (w u v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hu : u ∈ forestCollisionProfiles n L x)
    (hv : v ∈ forestCollisionProfiles n L x)
    (hwcompat : ∀ i, i ≠ j → Even (w i).val) (hucompat : ∀ i, i ≠ j → Even (u i).val)
    (a c : β) (hac : a ≠ c) (ha : 2^(L a)-1 < (w a).val) (hc : 2^(L c)-1 < (u c).val)
    (hvlow : ∀ i, (v i).val ≤ 2^(L i)-1) :
    (∀ i, i ≠ j → (v i).val=0) ∧
      (v j).val+1 ≤ (w j).val+1 ∧ (v j).val+1 ≤ (u j).val+1 ∧
      2^(L a) • x a+((w j).val+1) • x j=((v j).val+1) • x j ∧
      2^(L c) • x c+((u j).val+1) • x j=((v j).val+1) • x j := by
  classical
  obtain ⟨haj,hwa,hwz,_,_,_⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j hwidth w hw hwcompat a ha
  obtain ⟨hcj,huc,huz,_,_,_⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j hwidth u hu hucompat c hc
  have hsmall : ∀ z ∈ forestCollisionProfiles n L x, (z j).val < 2^(L j) := by
    intro z hz
    have hm : (∑ i, (z i).val)<n ∧
        (∑ i, (z i).val • x i)=∑ i, (2^(L i)-1) • x i := by
      simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hz
    have := Finset.single_le_sum (f := fun i ↦ (z i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hva := no_overflow_profile_zero_on_strip_arm L hL hwide g hg E x b hchain j a haj w v hw hv (hsmall w hw) hwa hwz hvlow
  have hvc := no_overflow_profile_zero_on_strip_arm L hL hwide g hg E x b hchain j c hcj u v hu hv (hsmall u hu) huc huz hvlow
  have hfull : ({j,a,c} : Finset β)=Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simp [hr,Ne.symm haj,Ne.symm hcj,hac]
  have hvz : ∀ i, i ≠ j → (v i).val=0 := by
    intro i hij
    have hi : i ∈ ({j,a,c} : Finset β) := by rw [hfull]; exact Finset.mem_univ _
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi
    rcases hi with hi | hi | hi
    · exact False.elim (hij hi)
    · exact hi.symm ▸ hva
    · exact hi.symm ▸ hvc
  exact ⟨hvz,
    axis_profile_height_le_compatible_strip_height hr L hL hwide g hg E x b hchain hgen j hwidth w v hw hv hwcompat a ha hvz,
    axis_profile_height_le_compatible_strip_height hr L hL hwide g hg E x b hchain hgen j hwidth u v hu hv hucompat c hc hvz,
    axis_profile_strip_boundary_relation L x j a haj w v hw hv hwa hwz hvz,
    axis_profile_strip_boundary_relation L x j c hcj u v hu hv huc huz hvz⟩

/-- Boundary savings need only the aggregate remaining coin capacity,
so the escaping arm itself may be arbitrarily short. -/
theorem not_validTuple_of_boundary_savings_with_joint_capacity
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (c : β → ℕ) (hc : ∀ i, c i < 2^(L i)) (hca : c a=0)
    (hrel : 2^(L a) • x a=∑ i, c i • x i)
    (hcap : n ≤ (∑ i, (2^(L i)-1-c i))+2^(L a))
    (u : β → ℕ → ℕ) (hu : ∀ i, val (L i) (u i)=2^(L i)-1-c i)
    (hus : Supp (L a) (u a)) (save : β → ℕ)
    (hcost : ∀ i, dsum (L i) (u i)+save i ≤ L i) (hsave : 2 ≤ ∑ i, save i) :
    ¬ ValidTuple g := by
  classical
  obtain ⟨v,hvs,hv,hvd⟩ := exists_binary_rep_add_two_top_coins (hL a) (u a) hus
  let X := fun i ↦ 2^(L i)-1-c i+(if i=a then 2^(L a) else 0)
  let w := fun i ↦ if i=a then v else u i
  have hw : ∀ i, val (L i) (w i)=X i := by
    intro i
    by_cases hi : i=a
    · subst i
      simpa only [w,X,if_pos rfl,if_true,hu] using hv
    · simp only [w,X,if_neg hi,add_zero,hu]
  have hwd : ∀ i, dsum (L i) (w i)=dsum (L i) (u i)+(if i=a then 2 else 0) := by
    intro i
    by_cases hi : i=a
    · subst i; simpa only [w,if_pos rfl,if_true] using hvd
    · simp only [w,if_neg hi,add_zero]
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hcost i)
  rw [Finset.sum_add_distrib,hsize] at hs
  have hlow : (∑ i, dsum (L i) (w i)) ≤ n := by
    simp only [hwd,Finset.sum_add_distrib]
    have hh : (∑ i : β, if i=a then 2 else 0)=2 := by simp
    rw [hh]
    omega
  have hhigh : n ≤ ∑ i, X i := by
    simpa only [X,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hcap
  have hneq : ∃ i, X i ≠ 2^(L i)-1 := by
    refine ⟨a,?_⟩
    have hp : 0 < 2^(L a) := by positivity
    simp only [X,hca,Nat.sub_zero,if_true]
    omega
  have hsum : (∑ i, X i • x i)=∑ i, (2^(L i)-1) • x i := by
    have hboundary : (∑ i, (if i=a then 2^(L a) else 0) • x i)=2^(L a) • x a := by
      simp only [ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    simp only [X,add_nsmul,Finset.sum_add_distrib,hboundary,hrel]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← add_nsmul,Nat.sub_add_cancel (by have := hc i; omega)]
  exact not_validTuple_of_chain_forest_integer_weights L X g E x b hchain w hw hlow hhigh hneq hsum


/-- A small bounded representation of a boundary in a wide forest can
involve at most one other seed, even for a short escaping arm. -/
theorem support_card_le_one_of_small_forest_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    (c : β → ℕ) (hc : ∀ i, c i < 2^(L i)) (hca : c a=0)
    (hrel : 2^(L a) • x a=∑ i, c i • x i) (hsmall : (∑ i, c i)<n) :
    (Finset.univ.filter (fun i ↦ 0 < c i)).card ≤ 1 := by
  classical
  have hrep : ∀ i, ∃ u, Supp (L i) u ∧ val (L i) u=2^(L i)-1-c i ∧
      dsum (L i) u+(if 0 < c i then 1 else 0) ≤ L i := by
    intro i
    have hci := hc i
    have hLi := hL i
    by_cases hi : 0 < c i
    · obtain ⟨u,hs,hu,hdu⟩ := exists_rep_lt (L i) (2^(L i)-1-c i) (by omega)
      exact ⟨u,hs,hu,by simp only [if_pos hi]; omega⟩
    · have hz : c i=0 := by omega
      obtain ⟨u,hs,hu,hdu⟩ := exists_rep_le (L i) (2^(L i)-1-c i) (by
        have hp : 0 < 2^(L i) := by positivity
        omega)
      exact ⟨u,hs,hu,by simpa only [if_neg hi,add_zero] using hdu⟩
  choose u hs hu hcost using hrep
  by_contra hnot
  have hsave : 2 ≤ ∑ i, if 0 < c i then 1 else 0 := by
    have hh : (∑ i, if 0 < c i then 1 else 0)=(Finset.univ.filter (fun i ↦ 0 < c i)).card := by simp
    rw [hh]
    omega
  have hcap : n ≤ (∑ i, (2^(L i)-1-c i))+2^(L a) := by
    have hh : (∑ i, (2^(L i)-1-c i))+(∑ i, c i)=∑ i, (2^(L i)-1) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact Nat.sub_add_cancel (by have := hc i; omega)
    have := Nat.two_pow_pos (L a)
    omega
  exact not_validTuple_of_boundary_savings_with_joint_capacity L hL g E x b hchain a c hc hca hrel hcap
    u hu (hs a) (fun i ↦ if 0 < c i then 1 else 0) hcost hsave hg


/-- A genuine boundary is excluded from every NONZERO small box face
on the other arms. Joint capacity replaces any all-long hypothesis. -/
theorem genuine_forest_boundary_not_small_other_box
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (a : β) (c : β → ℕ) (hc : ∀ i, c i < 2^(L i)) (hca : c a=0)
    (hsmall : (∑ i, c i)<n) (hpos : ∃ j, 0 < c j) :
    2^(L a) • x a ≠ ∑ i, c i • x i := by
  classical
  intro he
  have hs := support_card_le_one_of_small_forest_boundary L hL g hg E x b hchain a hwide c hc hca he hsmall
  obtain ⟨j,hj⟩ := hpos
  have hz : ∀ i, i ≠ j → c i=0 := by
    intro i hij
    by_contra hn
    apply hij
    exact Finset.card_le_one.mp hs i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩)
      j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩)
  have hsum : (∑ i, c i • x i)=c j • x j := by
    apply Finset.sum_eq_single j
    · intro i _ hij; rw [hz i hij,zero_nsmul]
    · simp
  have hcn : c j < n := lt_of_le_of_lt (Finset.single_le_sum (f := c) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)) hsmall
  have haj : a ≠ j := by intro h; subst j; omega
  exact genuine_forest_boundary_not_small_axis_weight L hL hwide g hg E x b hchain hgen a j haj
    (c j) hj hcn (hc j) (by rwa [hsum] at he)

/-- Any no-overflow profile coexisting with a compatible strip has
strictly smaller dominant height, unless the heights are equal, the
no-overflow profile lies on the axis, and the strip boundary is zero.
This derives the axis conclusion in the equality case. -/
theorem no_overflow_profile_below_strip_or_equal_zero_boundary
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (j : β) (hwidth : n ≤ 2^(L j))
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hcompat : ∀ i, i ≠ j → Even (w i).val)
    (a : β) (ha : 2^(L a)-1 < (w a).val)
    (hvlow : ∀ i, (v i).val ≤ 2^(L i)-1) :
    (v j).val+1 < (w j).val+1 ∨
      ((v j).val=(w j).val ∧ (∀ i, i ≠ j → (v i).val=0) ∧ 2^(L a) • x a=0) := by
  classical
  by_cases hvj : (v j).val < (w j).val
  · exact Or.inl (by omega)
  right
  obtain ⟨haj,hwa,hwz,_,_,_⟩ := compatible_overflow_profile_strip_shape hr L hL g hg E x b hchain j hwidth w hw hcompat a ha
  have hwm : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hvm : (∑ i, (v i).val)<n ∧
      (∑ i, (v i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hv
  have hwj : (w j).val < 2^(L j) := by
    have := Finset.single_le_sum (f := fun i ↦ (w i).val) (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ j)
    omega
  have hva := no_overflow_profile_zero_on_strip_arm L hL hwide g hg E x b hchain j a haj w v hw hv hwj hwa hwz hvlow
  let C : β → ℕ := fun i ↦ if i=j then (v i).val-(w j).val else (v i).val
  have hC : ∀ i, C i < 2^(L i) := by
    intro i
    have := hvlow i
    dsimp only [C]
    split_ifs <;> have := Nat.two_pow_pos (L i) <;> omega
  have hCa : C a=0 := by simp only [C,if_neg haj,hva]
  have hCsmall : (∑ i, C i)<n := by
    apply lt_of_le_of_lt (Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ ?_)) hvm.1
    dsimp only [C]
    split_ifs <;> omega
  have hCpoint : ∀ i, C i+(if i=j then (w j).val else 0)=(v i).val := by
    intro i
    by_cases hij : i=j
    · subst i; simp only [C,if_true]; omega
    · simp only [C,if_neg hij,add_zero]
  have hCsum : (∑ i, C i • x i)+(w j).val • x j=∑ i, (v i).val • x i := by
    calc
      _=∑ i, (C i+(if i=j then (w j).val else 0)) • x i := by simp [add_nsmul,ite_smul,Finset.sum_add_distrib]
      _=_ := by simp only [hCpoint]
  have hws : (∑ i, (w i).val • x i)=(w j).val • x j+2^(L a) • x a := by
    calc
      _ = ∑ i, ((if i=j then (w j).val • x j else 0)+(if i=a then 2^(L a) • x a else 0)) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i=j
        · subst i; simp [Ne.symm haj]
        · by_cases hia : i=a
          · subst i; simp [haj,hwa]
          · simp [hij,hia,hwz i hij hia]
      _ = _ := by simp [Finset.sum_add_distrib]
  have hrel : 2^(L a) • x a=∑ i, C i • x i := by
    apply add_right_cancel (b := (w j).val • x j)
    calc
      _=∑ i, (w i).val • x i := by rw [hws]; abel
      _=∑ i, (v i).val • x i := hwm.2.trans hvm.2.symm
      _=_ := hCsum.symm
  have hz : ∀ i, C i=0 := by
    intro i
    by_contra hn
    exact genuine_forest_boundary_not_small_other_box L hL hwide g hg E x b hchain hgen
      a C hC hCa hCsmall ⟨i,by omega⟩ hrel
  refine ⟨?_,?_,?_⟩
  · have hh := hz j
    simp only [C,if_true] at hh
    omega
  · intro i hij
    simpa only [C,if_neg hij] using hz i
  · simpa only [hz,zero_nsmul,Finset.sum_const_zero] using hrel

end MinModulus
