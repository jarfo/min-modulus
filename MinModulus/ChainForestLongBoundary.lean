import MinModulus.ChainForestTwoLongArms

/-! A sufficiently long genuine boundary is missing from the entire
ordinary forest box whenever it is nonzero. Boundary representations
may use their own chain: the stronger width threshold pays for this
previously excluded pivot. The unrestricted conjecture remains open. -/

namespace MinModulus
open Finset

/-- Two aggregate complement savings pay for the extra two top coins
at a represented forest boundary. This gives an actual rival in the
original group with all affine data and all chains retained. -/
theorem not_validTuple_of_long_chain_boundary_savings
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n ≤ 2^(L a))
    (c : β → ℕ) (hc : ∀ i, c i < 2^(L i))
    (hrel : 2^(L a) • x a=∑ i, c i • x i)
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
    have hh := Finset.single_le_sum (f := X) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    have hXa : 2^(L a) ≤ X a := by
      simp only [X,if_true]
      have := hc a
      omega
    exact hcap.trans (hXa.trans hh)
  have hneq : ∃ i, X i ≠ 2^(L i)-1 := by
    refine ⟨a,?_⟩
    have hp : 0 < 2^(L a) := by positivity
    simp only [X,if_true]
    have := hc a
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

/-- A sufficiently capacious positive boundary representation can
involve at most one seed, including the boundary seed. Two positive
complements already save the coins needed for an actual far-side rival. -/
theorem support_card_le_one_of_valid_long_chain_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n ≤ 2^(L a))
    (c : β → ℕ) (hc : ∀ i, c i < 2^(L i))
    (hrel : 2^(L a) • x a=∑ i, c i • x i) :
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
  exact not_validTuple_of_long_chain_boundary_savings L hL g E x b hchain a hcap c hc hrel
    u hu (hs a) (fun i ↦ if 0 < c i then 1 else 0) hcost hsave hg

/-- Every positive boundary coefficient is a power of two. The
non-power complement would save the two extra boundary coins. -/
theorem power_coefficient_of_valid_long_chain_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n ≤ 2^(L a))
    (c : β → ℕ) (hc : ∀ i, c i < 2^(L i))
    (hrel : 2^(L a) • x a=∑ i, c i • x i)
    (j : β) (hj : 0 < c j) : ∃ e, c j=2^e := by
  classical
  by_contra hnot
  have hLj : 2 ≤ L j := by
    by_contra h
    have hL1 : L j=1 := by have := hL j; omega
    have hci := hc j
    rw [hL1,pow_one] at hci
    have hc1 : c j=1 := by omega
    exact hnot ⟨0,by simpa using hc1⟩
  have hrep : ∀ i, ∃ u, Supp (L i) u ∧ val (L i) u=2^(L i)-1-c i ∧
      dsum (L i) u+(if i=j then 2 else 0) ≤ L i := by
    intro i
    by_cases hi : i=j
    · subst i
      obtain ⟨u,hs,hu,hdu⟩ := exists_rep_compl (L j) (c j) (hc j) hj.ne' hnot
      exact ⟨u,hs,hu,by simp only [if_true]; omega⟩
    · obtain ⟨u,hs,hu,hdu⟩ := exists_rep_le (L i) (2^(L i)-1-c i) (by
        have hp : 0 < 2^(L i) := by positivity
        omega)
      exact ⟨u,hs,hu,by simpa only [if_neg hi,add_zero] using hdu⟩
  choose u hs hu hcost using hrep
  exact not_validTuple_of_long_chain_boundary_savings L hL g E x b hchain a hcap c hc hrel
    u hu (hs a) (fun i ↦ if i=j then 2 else 0) hcost (by simp) hg

/-- Any NONZERO bounded positive representation of a capacious
chain boundary is one actual dyadic entry, possibly in the same chain. No unit,
arity, parity or supplied dyadic-coefficient premise is used. -/
theorem actual_entry_of_valid_nonzero_long_chain_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n ≤ 2^(L a))
    (c : β → ℕ) (hc : ∀ i, c i < 2^(L i))
    (hrel : 2^(L a) • x a=∑ i, c i • x i) (hpos : ∃ j, 0 < c j) :
    ∃ j : β, ∃ e : Fin (L j), 2^(L a) • x a=2^e.val • x j := by
  classical
  let S := Finset.univ.filter (fun i ↦ 0 < c i)
  have hcard : S.card ≤ 1 := support_card_le_one_of_valid_long_chain_boundary L hL g hg E x b hchain a hcap c hc hrel
  obtain ⟨j,hj⟩ := hpos
  have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hj⟩
  have hS : S={j} := Finset.eq_singleton_iff_unique_mem.mpr ⟨hjS,by
    intro i hi
    exact (Finset.card_le_one.mp hcard) i hi j hjS⟩
  have hzero : ∀ i, i ≠ j → c i=0 := by
    intro i hi
    by_contra hci
    have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
    rw [hS] at hiS
    exact hi (Finset.mem_singleton.mp hiS)
  obtain ⟨e,he⟩ := power_coefficient_of_valid_long_chain_boundary L hL g hg E x b hchain a hcap c hc hrel j hj
  have heL : e < L j := by
    by_contra h
    have hh := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : L j ≤ e)
    have hci := hc j
    rw [he] at hci
    omega
  refine ⟨j,⟨e,heL⟩,?_⟩
  rw [hrel]
  have hs : (∑ i, c i • x i)=c j • x j := by
    apply Finset.sum_eq_single j
    · intro i _ hi; rw [hzero i hi,zero_smul]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hs,he]

/-- A nonzero genuine endpoint of one wide arm lies outside the
entire ordinary box. Its representation may use the wide arm itself. -/
theorem long_genuine_boundary_not_in_box_of_nonzero
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n ≤ 2^(L a)) (hnz : 2^(L a) • x a ≠ 0)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i)) :
    (∑ i, p i • x i) ≠ 2^(L a) • x a := by
  classical
  intro he
  have hpos : ∃ i, 0 < p i := by
    by_contra hnot
    have hz : ∀ i, p i=0 := by push Not at hnot; intro i; have := hnot i; omega
    exact hnz (by simpa only [hz,zero_smul,Finset.sum_const_zero] using he.symm)
  obtain ⟨k,e,hentry⟩ := actual_entry_of_valid_nonzero_long_chain_boundary L hL g hg E x b hchain
    a hcap p hp he.symm hpos
  have htop : 2 • (g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)=2^(L a) • x a := by
    have hLa : L a-1+1=L a := by have := hL a; omega
    simp only [hchain,smul_smul,← pow_succ',hLa]
  apply hgenuine (E ⟨k,e⟩)
  have hk := hchain k e
  rw [← hentry,← htop,two_nsmul] at hk
  apply add_right_cancel (b := b)
  simp only [two_nsmul]
  abel_nf at hk ⊢
  exact hk

/-- A subbinary valid forest needs only one sufficiently wide genuine
arm to exclude its boundary from the ordinary box. -/
theorem boundary_not_in_box_of_subbinary_genuine_wide_arm
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (a : β) (ha : 2*n+1 ≤ 2^(L a))
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i)) :
    (∑ i, p i • x i) ≠ 2^(L a) • x a := by
  exact long_genuine_boundary_not_in_box_of_nonzero L hL g hg E x b hchain a (by omega)
    (boundary_ne_zero_of_subbinary_wide_arm L hL g hg E x b hchain hsub a ha) hgenuine p hp

/-- A small strict column deficit produces a full-length rival even
when the collision representation uses the boundary arm itself. -/
theorem not_validTuple_of_long_boundary_column_collision
    {n : ℕ} {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a j : β) (hja : j ≠ a) (hcap : n ≤ 2^(L a)) (hLj : 4 ≤ L j)
    (t : ℕ) (p : β → ℕ) (hp : ∀ i, p i < 2^(L i))
    (hpj : p j < t) (ht : t-p j ≤ 2^(L j-4))
    (heq : (∑ i, p i • x i)=2^(L a) • x a+t • x j) : ¬ ValidTuple g := by
  classical
  let X := fun i ↦ 2^(L i)-1-p i+(if i=a then 2^(L a) else if i=j then t else 0)
  have hXa : X a=2^(L a)-1-p a+2^(L a) := by simp [X]
  have hXj : X j=2^(L j)-1+(t-p j) := by
    simp only [X,if_neg hja,if_true]
    have := hp j
    omega
  have hrep : ∀ i, ∃ u, val (L i) u=X i ∧
      dsum (L i) u+(if i=j then 2 else 0) ≤ L i+(if i=a then 2 else 0) := by
    intro i
    by_cases hi : i=a
    · subst i
      obtain ⟨u,hs,hu,hdu⟩ := exists_rep_le (L a) (2^(L a)-1-p a) (by
        have h : 0 < 2^(L a) := by positivity
        omega)
      obtain ⟨v,_,hv,hdv⟩ := exists_binary_rep_add_two_top_coins (hL a) u hs
      refine ⟨v,by rw [hv,hu,hXa],?_⟩
      simp only [if_neg (Ne.symm hja),if_true,add_zero,hdv]
      omega
    · by_cases hij : i=j
      · subst i
        obtain ⟨u,_,hu,hdu⟩ := exists_binary_rep_all_ones_add_tiny hLj (by omega : 0 < t-p j) ht
        exact ⟨u,hu.trans hXj.symm,by simpa only [if_true,if_neg hja,add_zero] using hdu⟩
      · obtain ⟨u,_,hu,hdu⟩ := exists_rep_le (L i) (2^(L i)-1-p i)
          (by
            have h : 0 < 2^(L i) := by positivity
            omega)
        refine ⟨u,?_,?_⟩
        · simpa only [X,if_neg hi,if_neg hij,add_zero] using hu
        · simpa only [if_neg hi,if_neg hij,add_zero] using hdu
  choose u hu hcost using hrep
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hlow : (∑ i, dsum (L i) (u i)) ≤ n := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hcost i)
    simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,hsize] at hs
    omega
  have hhigh : n ≤ ∑ i, X i := by
    have hh := Finset.single_le_sum (f := X) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)
    rw [hXa] at hh
    omega
  have hneq : ∃ i, X i ≠ 2^(L i)-1 := by
    refine ⟨a,?_⟩
    rw [hXa]
    have h : 0 < 2^(L a) := by positivity
    have := hp a
    omega
  have hsum : (∑ i, X i • x i)=∑ i, (2^(L i)-1) • x i := by
    have hsplit : ∀ i, (if i=a then 2^(L a) else if i=j then t else 0) • x i=
        (if i=a then 2^(L a) • x a else 0)+(if i=j then t • x j else 0) := by
      intro i
      by_cases hi : i=a
      · subst i; simp [Ne.symm hja]
      · by_cases hij : i=j
        · subst i; simp [hja]
        · simp [hi,hij]
    simp only [X,add_nsmul,hsplit,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [← heq,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← add_nsmul,Nat.sub_add_cancel (by have := hp i; omega)]
  exact not_validTuple_of_chain_forest_integer_weights L X g E x b hchain u hu hlow hhigh hneq hsum


/-- Every tiny column point beside a nonzero genuine wide boundary
is missing from the ordinary box. The column arm need only have length four. -/
theorem tiny_column_not_in_box_of_long_genuine_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a j : β) (hja : j ≠ a)
    (ha : n ≤ 2^(L a)) (hLj : 4 ≤ L j) (hnz : 2^(L a) • x a ≠ 0)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (t : ℕ) (ht : t ≤ 2^(L j-4))
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i)) :
    (∑ i, p i • x i) ≠ 2^(L a) • x a+t • x j := by
  classical
  intro heq
  have hpj : p j < t := by
    by_contra hnot
    let P := fun i ↦ if i=j then p j-t else p i
    have hP : ∀ i, P i < 2^(L i) := by
      intro i
      by_cases hi : i=j
      · subst i; simpa only [P,if_pos rfl] using (Nat.sub_le (p j) t).trans_lt (hp j)
      · simpa only [P,if_neg hi] using hp i
    have hsum : (∑ i, P i • x i)+t • x j=∑ i, p i • x i := by
      have hs : ∀ i, p i • x i=P i • x i+(if i=j then t • x j else 0) := by
        intro i
        by_cases hi : i=j
        · subst i
          simp only [P,if_pos rfl,if_true]
          rw [← add_nsmul,Nat.sub_add_cancel (by omega)]
        · simp only [P,if_neg hi,add_zero]
      calc
        _=∑ i, (P i • x i+(if i=j then t • x j else 0)) := by
          simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
        _=_ := (Finset.sum_congr rfl (fun i _ ↦ hs i)).symm
    have hrep : (∑ i, P i • x i)=2^(L a) • x a := add_right_cancel (hsum.trans heq)
    exact long_genuine_boundary_not_in_box_of_nonzero L hL g hg E x b hchain a ha hnz hgenuine P hP hrep
  exact not_validTuple_of_long_boundary_column_collision L hL g E x b hchain a j hja
    ha hLj t p hp hpj (by omega) heq hg


/-- At subbinary group size a single wide genuine arm supplies
an exterior column along any other arm of length at least four. -/
theorem tiny_column_not_in_box_of_subbinary_genuine_wide_arm
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) (a j : β) (hja : j ≠ a)
    (ha : 2*n+1 ≤ 2^(L a)) (hLj : 4 ≤ L j)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (t : ℕ) (ht : t ≤ 2^(L j-4))
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i)) :
    (∑ i, p i • x i) ≠ 2^(L a) • x a+t • x j := by
  exact tiny_column_not_in_box_of_long_genuine_boundary L hL g hg E x b hchain a j hja
    (by omega) hLj (boundary_ne_zero_of_subbinary_wide_arm L hL g hg E x b hchain hsub a ha)
    hgenuine t ht p hp

end MinModulus
