import MinModulus.ChainForestRelations

/-! Arbitrary-arity boundary savings force a single dyadic actual rejoin.
Exact one-corner coverage consumes every tight long forest with at least
three genuine terminal chains, including axis corners. Direct original
G1 half descent is proved for the entire tight long three-chain class;
the remaining original residual has a short arm or strictly positive
packing slack. Unrestricted G1/G2/G3 remain open. -/

namespace MinModulus
open Finset

/-- Two aggregate complement savings pay for the extra two top coins
at a represented forest boundary. This gives an actual rival in the
original group with all affine data and all chains retained. -/
theorem not_validTuple_of_chain_forest_boundary_savings
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n ≤ (2^(L a)-1)+2^(L a))
    (c : β → ℕ) (hc : ∀ i, c i < 2^(L i)) (hca : c a=0)
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
    have hXa : X a=(2^(L a)-1)+2^(L a) := by simp only [X,hca,Nat.sub_zero,if_true]
    rw [hXa] at hh
    exact hcap.trans hh
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

/-- A sufficiently capacious positive boundary representation can
involve at most ONE other seed. Two positive complements already save
the coins needed for an actual far-side rival. -/
theorem support_card_le_one_of_valid_chain_forest_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n ≤ (2^(L a)-1)+2^(L a))
    (c : β → ℕ) (hc : ∀ i, c i < 2^(L i)) (hca : c a=0)
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
  exact not_validTuple_of_chain_forest_boundary_savings L hL g E x b hchain a hcap c hc hca hrel
    u hu (hs a) (fun i ↦ if 0 < c i then 1 else 0) hcost hsave hg

/-- Every positive boundary coefficient is a power of two. The
non-power complement would save the two extra boundary coins. -/
theorem power_coefficient_of_valid_forest_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n ≤ (2^(L a)-1)+2^(L a))
    (c : β → ℕ) (hc : ∀ i, c i < 2^(L i)) (hca : c a=0)
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
  exact not_validTuple_of_chain_forest_boundary_savings L hL g E x b hchain a hcap c hc hca hrel
    u hu (hs a) (fun i ↦ if i=j then 2 else 0) hcost (by simp) hg

/-- Any NONZERO bounded positive representation of a capacious
chain boundary is one actual dyadic entry in another chain. No unit,
arity, parity or supplied dyadic-coefficient premise is used. -/
theorem actual_entry_of_valid_positive_forest_boundary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (hcap : n ≤ (2^(L a)-1)+2^(L a))
    (c : β → ℕ) (hc : ∀ i, c i < 2^(L i)) (hca : c a=0)
    (hrel : 2^(L a) • x a=∑ i, c i • x i) (hpos : ∃ j, 0 < c j) :
    ∃ j : β, j ≠ a ∧ ∃ e : Fin (L j), 2^(L a) • x a=2^e.val • x j := by
  classical
  let S := Finset.univ.filter (fun i ↦ 0 < c i)
  have hcard : S.card ≤ 1 := support_card_le_one_of_valid_chain_forest_boundary L hL g hg E x b hchain a hcap c hc hca hrel
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
  obtain ⟨e,he⟩ := power_coefficient_of_valid_forest_boundary L hL g hg E x b hchain a hcap c hc hca hrel j hj
  have heL : e < L j := by
    by_contra h
    have hh := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : L j ≤ e)
    have hci := hc j
    rw [he] at hci
    omega
  refine ⟨j,by intro h; subst j; omega,⟨e,heL⟩,?_⟩
  rw [hrel]
  have hs : (∑ i, c i • x i)=c j • x j := by
    apply Finset.sum_eq_single j
    · intro i _ hi; rw [hzero i hi,zero_smul]
    · intro h; exact (h (Finset.mem_univ _)).elim
  rw [hs,he]

/-- Exact one-corner packing gives ACTUAL full box coverage in any
finite abelian group. Every boundary is therefore represented, without
a supplied cover or individual-unit premise. -/
theorem exists_box_representation_of_tight_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0)
    (htight : Fintype.card G+(∏ i, (2^(L i)-d i))=2^n) (z : G) :
    ∃ p : β → ℕ, (∀ i, p i < 2^(L i)) ∧ (∑ i, p i • x i)=z := by
  classical
  let B := ∀ i, Fin (2^(L i))
  let C : B → Prop := fun p ↦ ∀ i, d i ≤ (p i).val
  let R := {p : B // ¬ C p}
  let f : R → G := fun p ↦ ∑ i, (p.val i).val • x i
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hbox : Fintype.card B=2^n := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum,hsize]
  let CE : {p : B // C p} ≃ (∀ i, Fin (2^(L i)-d i)) :=
    { toFun := fun p i ↦ ⟨(p.val i).val-d i,by have := (p.val i).isLt; have := p.property i; omega⟩
      invFun := fun p ↦ ⟨fun i ↦ ⟨(p i).val+d i,by have := (p i).isLt; have := hd i; omega⟩,
        fun i ↦ Nat.le_add_left _ _⟩
      left_inv := by
        intro p
        apply Subtype.ext
        funext i
        apply Fin.ext
        exact Nat.sub_add_cancel (p.property i)
      right_inv := by
        intro p
        funext i
        apply Fin.ext
        exact Nat.add_sub_cancel_right _ _ }
  have hcorner : Fintype.card {p : B // C p}=∏ i, (2^(L i)-d i) := by
    rw [Fintype.card_congr CE,Fintype.card_pi]
    simp only [Fintype.card_fin]
  have hR : Fintype.card R=Fintype.card G := by
    change Fintype.card {p : B // ¬ C p}=Fintype.card G
    rw [Fintype.card_subtype_compl C,hbox,hcorner]
    omega
  have hfi : Function.Injective f := by
    have aux (p q : R) (he : f p=f q)
        (hle : ∀ i, (p.val i).val ≤ (q.val i).val) : p=q := by
      by_contra hne
      let u := fun i ↦ (q.val i).val-(p.val i).val
      have hu : ∀ i, u i < 2^(L i) := fun i ↦ (Nat.sub_le _ _).trans_lt (q.val i).isLt
      have hupos : ∃ i, 0 < u i := by
        by_contra hnot
        push Not at hnot
        apply hne
        apply Subtype.ext
        funext i
        apply Fin.ext
        have h0 : (q.val i).val-(p.val i).val ≤ 0 := hnot i
        have := hle i
        omega
      have huzero := zero_relation_of_ordered_box_collision x
        (fun i ↦ (p.val i).val) (fun i ↦ (q.val i).val) hle he
      have heq := unique_nonzero_box_relation_of_valid_long_chain_forest L hL hlong hwide
        g hg E x b hchain d u hd hu hdpos hupos hdzero huzero
      apply q.property
      intro i
      have hh := congrFun heq i
      dsimp only [u] at hh
      omega
    intro p q he
    rcases box_fibres_ordered_of_valid_long_chain_forest L hL hlong g hg E x b hchain
        (fun i ↦ (p.val i).val) (fun i ↦ (q.val i).val)
        (fun i ↦ (p.val i).isLt) (fun i ↦ (q.val i).isLt) he with h | h
    · exact aux p q he h
    · exact (aux q p he.symm h).symm
  have hsurj : Function.Surjective f := by
    by_contra hnot
    have hh := Fintype.card_lt_of_injective_not_surjective f hfi hnot
    omega
  obtain ⟨p,hp⟩ := hsurj z
  exact ⟨fun i ↦ (p.val i).val,fun i ↦ (p.val i).isLt,hp⟩

/-- A represented boundary has ZERO coefficient on its own seed
when the actual zero relation involves that seed and another seed.
Mixed-relation exclusion and uniqueness also consume the pure-axis
alternative; an interior-corner assumption is not needed. -/
theorem pivot_eq_zero_of_box_boundary_representation
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdzero : (∑ i, d i • x i)=0)
    (a j : β) (hda : 0 < d a) (hdj : 0 < d j) (hja : j ≠ a)
    (c : β → ℕ) (hc : ∀ i, c i < 2^(L i))
    (hrel : 2^(L a) • x a=∑ i, c i • x i) : c a=0 := by
  classical
  by_contra hca
  have hcapos : 0 < c a := by omega
  let p := fun i ↦ if i=a then 2^(L a)-c a else 0
  let q := fun i ↦ if i=a then 0 else c i
  have hp : ∀ i, p i < 2^(L i) := by
    intro i
    by_cases hi : i=a
    · subst i; simp only [p,if_true]; have := hc a; omega
    · simp only [p,if_neg hi]; positivity
  have hq : ∀ i, q i < 2^(L i) := by
    intro i
    by_cases hi : i=a
    · subst i; simp only [q,if_true]; positivity
    · simpa only [q,if_neg hi] using hc i
  have hppos : ∃ i, 0 < p i := by
    refine ⟨a,?_⟩
    simp only [p,if_true]
    have := hc a
    omega
  have hdis : ∀ i, p i=0 ∨ q i=0 := by
    intro i
    by_cases hi : i=a
    · exact Or.inr (by simp only [q,if_pos hi])
    · exact Or.inl (by simp only [p,if_neg hi])
  have hpsum : (∑ i, p i • x i)=(2^(L a)-c a) • x a := by
    simp only [p,ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have hqsum : c a • x a+(∑ i, q i • x i)=∑ i, c i • x i := by
    calc
      _=(∑ i : β, if i=a then c a • x a else 0)+(∑ i, q i • x i) := by simp
      _=∑ i, ((if i=a then c a • x a else 0)+q i • x i) := by rw [Finset.sum_add_distrib]
      _=_ := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i=a
        · subst i; simp only [q,if_true,zero_smul,add_zero]
        · simp only [q,if_neg hi,zero_add]
  have hpq : (∑ i, p i • x i)=∑ i, q i • x i := by
    apply add_left_cancel (a := c a • x a)
    rw [hpsum,← add_nsmul,Nat.add_sub_of_le (hc a).le,hrel]
    exact hqsum.symm
  by_cases hqpos : ∃ i, 0 < q i
  · exact mixed_seed_relation_ne_of_valid_long_chain_forest L hL hlong g hg E x b hchain
      p q hp hq hdis hppos hqpos hpq
  · have hqzero : ∀ i, q i=0 := by intro i; by_contra h; exact hqpos ⟨i,by omega⟩
    have hpzero : (∑ i, p i • x i)=0 := by simpa only [hqzero,zero_smul,Finset.sum_const_zero] using hpq
    have heq := unique_nonzero_box_relation_of_valid_long_chain_forest L hL hlong hwide
      g hg E x b hchain d p hd hp ⟨a,hda⟩ hppos hdzero hpzero
    have hh := congrFun heq j
    simp only [p,if_neg hja] at hh
    omega

/-- A long-chain boundary cannot be zero when the actual bounded
zero relation contains that seed and another seed. Axis corners remain
allowed elsewhere in the relation. -/
theorem boundary_ne_zero_of_two_supported_box_relation
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdzero : (∑ i, d i • x i)=0)
    (a j : β) (hda : 0 < d a) (hdj : 0 < d j) (hja : j ≠ a) :
    2^(L a) • x a ≠ 0 := by
  intro hz
  have hh := pivot_eq_zero_of_box_boundary_representation L hL hlong hwide g hg E x b hchain
    d hd hdzero a j hda hdj hja d hd (hz.trans hdzero.symm)
  omega

/-- Exact corner coverage forces an ACTUAL endpoint rejoin at every
seed supported together with another seed in the zero relation. The
positive boundary coefficient and its dyadic form are both extracted. -/
theorem actual_rejoin_of_tight_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdzero : (∑ i, d i • x i)=0)
    (a j : β) (hda : 0 < d a) (hdj : 0 < d j) (hja : j ≠ a)
    (htight : Fintype.card G+(∏ i, (2^(L i)-d i))=2^n) :
    ∃ t : Fin n, g t=2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
  obtain ⟨c,hc,hrel⟩ := exists_box_representation_of_tight_long_chain_forest L hL hlong hwide
    g hg E x b hchain d hd ⟨a,hda⟩ hdzero htight (2^(L a) • x a)
  have hca := pivot_eq_zero_of_box_boundary_representation L hL hlong hwide g hg E x b hchain
    d hd hdzero a j hda hdj hja c hc hrel.symm
  have hpos : ∃ i, 0 < c i := by
    by_contra hnot
    have hz : ∀ i, c i=0 := by intro i; by_contra hi; exact hnot ⟨i,by omega⟩
    have hzero : 2^(L a) • x a=0 := by simpa only [hz,zero_smul,Finset.sum_const_zero] using hrel.symm
    exact boundary_ne_zero_of_two_supported_box_relation L hL hlong hwide g hg E x b hchain
      d hd hdzero a j hda hdj hja hzero
  have hcap : n ≤ (2^(L a)-1)+2^(L a) := (hlong a).trans (Nat.le_add_left _ _)
  obtain ⟨k,hka,e,he⟩ := actual_entry_of_valid_positive_forest_boundary L hL g hg E x b hchain a hcap c hc hca hrel.symm hpos
  refine ⟨E ⟨k,e⟩,?_⟩
  have hseed := hchain a ⟨L a-1,by have := hL a; omega⟩
  have ht := hchain k e
  have hdouble : 2 • (2^(L a-1) • x a)=2^(L a) • x a := by
    rw [← mul_nsmul,← pow_succ,show L a-1+1=L a by have := hL a; omega]
  have hh := congrArg (fun v : G ↦ 2 • v) hseed
  rw [hdouble,he] at hh
  rw [← ht] at hh
  simp only [two_nsmul] at hh ⊢
  apply add_right_cancel (b := b)
  calc
    _=(g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)+
        (g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) := hh.symm
    _=_ := by abel

/-- With at least three long chains, EVERY nonzero bounded zero
relation involves at least two seeds. Two untouched long chains would
already provide enough complementary weight for a full-length rival.
This retains axis corners instead of assuming strict interiority. -/
theorem exists_two_supported_coordinates_of_long_forest_zero_relation
    {n : ℕ} (hn : 2 ≤ n) {β : Type*} [Fintype β] (hr : 3 ≤ Fintype.card β)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0) :
    ∃ a j, 0 < d a ∧ 0 < d j ∧ j ≠ a := by
  classical
  obtain ⟨a,ha⟩ := hdpos
  have hs := small_complement_of_zero_relation_of_valid_chain_forest L hL g hg E x b hchain d hd ⟨a,ha⟩ hdzero
  by_contra hnot
  have hz : ∀ j, j ≠ a → d j=0 := by
    intro j hj
    by_contra hdj
    exact hnot ⟨a,j,ha,by omega,hj⟩
  let W := fun i ↦ 2^(L i)-1-d i
  have hsub : (∑ i ∈ Finset.univ.erase a, W i) ≤ ∑ i, W i :=
    Finset.sum_le_sum_of_subset (Finset.erase_subset a Finset.univ)
  have hlow : (Finset.univ.erase a).card*(n-1) ≤ ∑ i ∈ Finset.univ.erase a, W i := by
    calc
      _=∑ _i ∈ Finset.univ.erase a, (n-1) := by simp
      _≤_ := by
        apply Finset.sum_le_sum
        intro i hi
        have hia := (Finset.mem_erase.mp hi).1
        have hdi := hz i hia
        have hh := hlong i
        dsimp only [W]
        omega
  have hcard : (Finset.univ.erase a).card=Fintype.card β-1 := by simp
  rw [hcard] at hlow
  have hc : 2 ≤ Fintype.card β-1 := by omega
  have htwo := Nat.mul_le_mul_right (n-1) hc
  change (∑ i, W i) < n at hs
  omega

/-- Three or more positive long arms automatically make the full
binary box wide enough for uniqueness. Pure geometry suffices. -/
theorem box_wide_of_three_le_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (hr : 3 ≤ Fintype.card β)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) : 2*n ≤ ∑ i, (2^(L i)-1) := by
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hcount : Fintype.card β ≤ ∑ i, L i := by
    calc
      _=∑ _i : β, (1 : ℕ) := by simp
      _≤_ := Finset.sum_le_sum (fun i _ ↦ hL i)
  have hn : 3 ≤ n := by omega
  have hh : (∑ _i : β, (n-1)) ≤ ∑ i, (2^(L i)-1) := by
    apply Finset.sum_le_sum
    intro i _
    have := hlong i
    omega
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hh
  have hthree := Nat.mul_le_mul_right (n-1) hr
  omega

/-- ANY tight long forest with at least three chains has an actual
endpoint rejoin. Exact coverage, nonzero support and boundary rigidity
are all conclusions, not additional hypotheses. -/
theorem exists_actual_rejoin_of_tight_long_forest_three_le
    {n : ℕ} (hn : 2 ≤ n) {β : Type*} [Fintype β] (hr : 3 ≤ Fintype.card β)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0)
    (htight : Fintype.card G+(∏ i, (2^(L i)-d i))=2^n) :
    ∃ a : β, ∃ t : Fin n, g t=2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
  have hwide := box_wide_of_three_le_long_chain_forest hr L hL hlong E
  obtain ⟨a,j,ha,hj,hja⟩ := exists_two_supported_coordinates_of_long_forest_zero_relation
    hn hr L hL hlong g hg E x b hchain d hd hdpos hdzero
  obtain ⟨t,ht⟩ := actual_rejoin_of_tight_long_chain_forest L hL hlong hwide g hg E x b hchain
    d hd hdzero a j ha hj hja htight
  exact ⟨a,t,ht⟩

/-- Genuine terminal forests with at least three long chains have
STRICTLY positive packing slack. Tightness is consumed by an actual
endpoint rejoin, including every axis-corner shape. -/
theorem strict_box_card_bound_of_genuine_long_chain_forest
    {n : ℕ} (hn : 2 ≤ n) {β : Type*} [Fintype β] (hr : 3 ≤ Fintype.card β)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0) :
    2^n < Fintype.card G+(∏ i, (2^(L i)-d i)) := by
  have hwide := box_wide_of_three_le_long_chain_forest hr L hL hlong E
  have hbound := box_card_bound_of_valid_long_chain_forest L hL hlong hwide g hg E x b hchain d hd hdpos hdzero
  by_contra hnot
  have htight : Fintype.card G+(∏ i, (2^(L i)-d i))=2^n := by omega
  obtain ⟨a,t,ht⟩ := exists_actual_rejoin_of_tight_long_forest_three_le hn hr L hL hlong
    g hg E x b hchain d hd hdpos hdzero htight
  exact hgenuine a t ht

/-- Direct ORIGINAL-G1 consumer for the entire tight long three-chain
class, including axis corners. Failed half descent makes the extracted
endpoints genuine, contradicting the forced actual rejoin. -/
theorem admitsValidTuple_half_of_critical_tight_long_three_chain_forest
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (L : A → ℕ) (hL : ∀ a, 0 < L a) (hlong : ∀ a, n+1 ≤ 2^(L a))
    (E : (Σ a : A, Fin (L a)) ≃ Fin (n+1)) (x : A → ZMod (2^(s+1)*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hend : ∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val)
    (d : A → ℕ) (hd : ∀ a, d a < 2^(L a)) (hdpos : ∃ a, 0 < d a)
    (hdzero : (∑ a, d a • x a)=0)
    (htight : 2^(s+1)*q+(∏ a, (2^(L a)-d a))=2^(n+1)) :
    AdmitsValidTuple n (2^s*q) := by
  classical
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,hgenuine⟩ := exact_three_genuine_escapes_of_critical_without_half hq g hg hc A hA b hclosed hnohalf
  have hr : 3 ≤ Fintype.card A := by simp only [Fintype.card_coe,hcard,le_refl]
  have hT : Fintype.card (ZMod (2^(s+1)*q))+(∏ a, (2^(L a)-d a))=2^(n+1) := by
    simpa only [ZMod.card] using htight
  obtain ⟨a,t,ht⟩ := exists_actual_rejoin_of_tight_long_forest_three_le (by omega) hr L hL hlong
    g hg E x b hchain d hd hdpos hdzero hT
  have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
  rw [he] at ht
  exact hgenuine a.val a.property t ht

/-- The ORIGINAL no-half three-escape G1 residual now supplies either
a short arm or a small dyadic-sided corner with STRICTLY POSITIVE
packing slack. Every tight long-forest case is consumed, including axes;
no normal form, relation, unit or interior-corner premise is added. -/
theorem exists_short_arm_or_positive_slack_of_critical_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    A.card=3 ∧ ∃ L : A → ℕ, (∀ a, 0 < L a) ∧ (∑ a, L a)=n+1 ∧
      ∃ E : (Σ a : A, Fin (L a)) ≃ Fin (n+1), ∃ x : A → ZMod (2^(s+1)*q),
      (∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) ∧
      (∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val) ∧
      (∀ a : A, ∀ j, g j ≠ 2 • g a.val+b) ∧
      2 ≤ (Finset.univ.filter (fun a ↦ Odd (x a).val)).card ∧
      AddSubgroup.closure (Set.range x)=⊤ ∧
      ((∃ a, 2^(L a) < n+1) ∨ ∃ d : A → ℕ, (∀ a, d a < 2^(L a)) ∧
        (∃ a, 0 < d a) ∧ (∑ a, d a • x a)=0 ∧ (∑ a, (2^(L a)-d a)) ≤ n+3 ∧
        (∃ a e, 2^(L a)-d a=2^e) ∧ 2^(n+1) < 2^(s+1)*q+∏ a, (2^(L a)-d a)) := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan⟩ :=
    exists_spanning_three_chain_forest_of_critical_without_half hq hn g hg hc A hA b hclosed hnohalf
  refine ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,?_⟩
  by_cases hlong : ∀ a, n+1 ≤ 2^(L a)
  · right
    have hN : Fintype.card (ZMod (2^(s+1)*q)) < 2^(n+1) := by
      rw [ZMod.card]
      exact lt_of_lt_of_le hc (by unfold stratumBound; exact Nat.sub_le _ _)
    obtain ⟨d,hd,hpos,hzero,hcorner⟩ :=
      exists_small_corner_relation_of_valid_subbinary_long_chain_forest L hL hlong g hg E x b hchain hN
    have hAr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
    have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
      intro a t
      have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
      rw [he]
      exact hgenuine a t
    have hp := strict_box_card_bound_of_genuine_long_chain_forest (by omega) (by omega : 3 ≤ Fintype.card A)
      L hL hlong g hg E x b hchain hgen d hd hpos hzero
    rw [hAr] at hcorner
    rw [ZMod.card] at hp
    exact ⟨d,hd,hpos,hzero,by omega,
      exists_power_corner_side_of_valid_chain_forest L hL g hg E x b hchain d hd hpos hzero,hp⟩
  · left
    simpa only [not_forall,not_le] using hlong

end MinModulus
