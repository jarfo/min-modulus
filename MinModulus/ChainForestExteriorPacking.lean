import MinModulus.ChainForestAxis

/-! Exterior columns supply exponentially many residues missing from
an actual long-chain binary box. The column charge closes all genuine
long three-chain forests at total length at least 67, giving the binary
bound in every finite abelian group and original G1 half descent in
every even stratum. Smaller long forests, short arms, higher escape
counts, and the unrestricted G1/G2/G3 inputs remain open. -/

namespace MinModulus
open Finset

/-- a short exterior-column collision has zero own-axis
coordinate. This is forced by ordered fibres and the same unique zero
relation, without any two-seed determinant argument. -/
theorem pivot_eq_zero_of_short_exterior_column_collision
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0)
    (a j : β) (hja : j ≠ a) (t : ℕ) (ht : t < d j)
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i))
    (heq : (∑ i, p i • x i)=2^(L a) • x a+t • x j) : p a=0 := by
  classical
  by_contra hnot
  let P : β → ℕ := fun i ↦ if i=a then 0 else p i
  let Q : β → ℕ := fun i ↦ if i=a then 2^(L a)-p a else if i=j then t else 0
  have hP : ∀ i, P i < 2^(L i) := by
    intro i
    dsimp only [P]
    split_ifs
    · positivity
    · exact hp i
  have hQ : ∀ i, Q i < 2^(L i) := by
    intro i
    dsimp only [Q]
    split_ifs with hi hij
    · subst i; have := hp a; omega
    · subst i; exact ht.trans (hd j)
    · positivity
  have hPsum : (∑ i, P i • x i)+p a • x a=∑ i, p i • x i := by
    have hsplit : ∀ i, p i • x i=P i • x i+(if i=a then p a • x a else 0) := by
      intro i
      by_cases hi : i=a <;> simp [P,hi]
    calc
      _=∑ i, (P i • x i+(if i=a then p a • x a else 0)) := by
        simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      _=_ := (Finset.sum_congr rfl (fun i _ ↦ hsplit i)).symm
  have hQsum : (∑ i, Q i • x i)=(2^(L a)-p a) • x a+t • x j := by
    have hsplit : ∀ i, Q i • x i=(if i=a then (2^(L a)-p a) • x a else 0)+
        (if i=j then t • x j else 0) := by
      intro i
      by_cases hi : i=a
      · subst i; simp [Q,Ne.symm hja]
      · by_cases hij : i=j
        · subst i; simp [Q,hja]
        · simp [Q,hi,hij]
    simp only [hsplit,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  have hPQ : (∑ i, P i • x i)=∑ i, Q i • x i := by
    apply add_right_cancel (b := p a • x a)
    rw [hPsum,heq,hQsum]
    have hsplit : (2^(L a)-p a) • x a+p a • x a=2^(L a) • x a := by
      rw [← add_nsmul,Nat.sub_add_cancel (hp a).le]
    calc
      _=((2^(L a)-p a) • x a+p a • x a)+t • x j := by rw [hsplit]
      _=_ := by abel
  have hle : ∀ i, P i ≤ Q i := by
    rcases box_fibres_ordered_of_valid_long_chain_forest L hL hlong g hg E x b hchain P Q hP hQ hPQ with h | h
    · exact h
    · have hh := h a
      simp only [P,Q,if_pos rfl] at hh
      have := hp a
      omega
  let u := fun i ↦ Q i-P i
  have hu : ∀ i, u i < 2^(L i) := fun i ↦ (Nat.sub_le _ _).trans_lt (hQ i)
  have hup : ∃ i, 0 < u i := by
    refine ⟨a,?_⟩
    simp only [u,Q,P,if_true,Nat.sub_zero]
    exact Nat.sub_pos_of_lt (hp a)
  have huz := zero_relation_of_ordered_box_collision x P Q hle hPQ
  have he := unique_nonzero_box_relation_of_valid_long_chain_forest L hL hlong hwide
    g hg E x b hchain d u hd hu hdpos hup hdzero huz
  have hh := congrFun he j
  simp only [u,Q,P,if_neg hja,if_true] at hh
  omega

/-- for a genuine supported endpoint, an exterior-column
collision has a STRICTLY negative coefficient in the shifted direction.
Otherwise it would represent the forbidden boundary in the ordinary box. -/
theorem shifted_coordinate_lt_of_genuine_exterior_column_collision
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdzero : (∑ i, d i • x i)=0)
    (a j : β) (hda : 0 < d a) (hdj : 0 < d j) (hja : j ≠ a)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (t : ℕ) (p : β → ℕ) (hp : ∀ i, p i < 2^(L i))
    (heq : (∑ i, p i • x i)=2^(L a) • x a+t • x j) : p j < t := by
  classical
  by_contra hnot
  have ht : t ≤ p j := by omega
  let P : β → ℕ := fun i ↦ if i=j then p j-t else p i
  have hP : ∀ i, P i < 2^(L i) := by
    intro i
    by_cases hi : i=j
    · subst i
      simpa only [P,if_pos rfl,if_true] using (Nat.sub_le (p j) t).trans_lt (hp j)
    · simpa only [P,if_neg hi] using hp i
  have hsum : (∑ i, P i • x i)+t • x j=∑ i, p i • x i := by
    have hs : ∀ i, p i • x i=P i • x i+(if i=j then t • x j else 0) := by
      intro i
      by_cases hi : i=j
      · subst i
        simp only [P,if_pos rfl,if_true]
        rw [← add_nsmul,Nat.sub_add_cancel ht]
      · simp only [P,if_neg hi,add_zero]
    calc
      _=∑ i, (P i • x i+(if i=j then t • x j else 0)) := by
        simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
      _=_ := (Finset.sum_congr rfl (fun i _ ↦ hs i)).symm
  have hrep : (∑ i, P i • x i)=2^(L a) • x a := add_right_cancel (hsum.trans heq)
  exact boundary_not_in_box_of_genuine_supported_long_chain_forest L hL hlong hwide
    g hg E x b hchain d hd hdzero a j hda hdj hja hgenuine P hP hrep

/-- a supported relation in ANOTHER arm makes this entire
seed interval injective. A smaller seed order would give a second
bounded zero relation with zero at the supported arm. -/
theorem seed_interval_injective_of_supported_other_long_forest_relation
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdzero : (∑ i, d i • x i)=0)
    (a j : β) (hda : 0 < d a) (hja : j ≠ a) :
    Function.Injective (fun t : Fin (2^(L j)) ↦ t.val • x j) := by
  classical
  have aux : ∀ t u : Fin (2^(L j)), t.val ≤ u.val → t.val • x j=u.val • x j → t=u := by
    intro t u hle he
    by_contra hne
    have hlt : t.val < u.val := by
      by_contra hnot
      exact hne (Fin.ext (by omega))
    let c : β → ℕ := fun i ↦ if i=j then u.val-t.val else 0
    have hc : ∀ i, c i < 2^(L i) := by
      intro i
      by_cases hi : i=j
      · subst i
        simpa only [c,if_pos rfl,if_true] using (Nat.sub_le u.val t.val).trans_lt u.isLt
      · simp only [c,if_neg hi]; positivity
    have hcpos : ∃ i, 0 < c i := ⟨j,by simpa only [c,if_pos rfl,if_true] using Nat.sub_pos_of_lt hlt⟩
    have hczero : (∑ i, c i • x i)=0 := by
      have hh : (u.val-t.val) • x j=0 := by
        apply add_left_cancel (a := t.val • x j)
        rw [← add_nsmul,Nat.add_sub_of_le hle,add_zero]
        exact he.symm
      simpa only [c,ite_smul,zero_smul,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hh
    have hh := unique_nonzero_box_relation_of_valid_long_chain_forest L hL hlong hwide
      g hg E x b hchain d c hd hc ⟨a,hda⟩ hcpos hdzero hczero
    have ha := congrFun hh a
    simp only [c,if_neg (Ne.symm hja)] at ha
    omega
  intro t u he
  rcases le_total t.val u.val with h | h
  · exact aux t u h he
  · exact (aux u t h he.symm).symm

/-- short-column cardinality supplies an ACTUAL collision
whenever slack is smaller than the shifted relation coefficient. This
works at arbitrary arity, without an assumed boundary representation. -/
theorem exists_short_exterior_column_collision_of_insufficient_slack
    {n : ℕ} {β : Type*} [Fintype β] [DecidableEq β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdzero : (∑ i, d i • x i)=0)
    (a j : β) (hda : 0 < d a) (hja : j ≠ a)
    (hsmall : Fintype.card G+(∏ i, (2^(L i)-d i)) < 2^n+d j) :
    ∃ t : ℕ, t < d j ∧ ∃ p : β → ℕ, (∀ i, p i < 2^(L i)) ∧
      (∑ i, p i • x i)=2^(L a) • x a+t • x j := by
  classical
  let w : Fin (d j) → G := fun t ↦ 2^(L a) • x a+t.val • x j
  have hi : Function.Injective w := by
    intro t u he
    have he' : t.val • x j=u.val • x j := add_left_cancel he
    have hh := seed_interval_injective_of_supported_other_long_forest_relation L hL hlong hwide
      g hg E x b hchain d hd hdzero a j hda hja
      (a₁ := ⟨t.val,t.isLt.trans (hd j)⟩) (a₂ := ⟨u.val,u.isLt.trans (hd j)⟩) he'
    have hv : t.val=u.val := congrArg (fun z : Fin (2^(L j)) ↦ z.val) hh
    exact Fin.ext hv
  let F := Finset.univ.image w
  have hc : F.card=d j := by simp only [F,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]
  by_contra hnot
  have havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) → (∑ i, p i • x i) ≠ z := by
    intro z hz p hp he
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
    exact hnot ⟨t.val,t.isLt,p,hp,he⟩
  have hh := box_card_bound_with_avoided_set_of_valid_long_chain_forest L hL hlong hwide
    g hg E x b hchain d hd ⟨a,hda⟩ hdzero F havoid
  rw [hc] at hh
  omega

/-- A sufficiently small positive shift saves two coins relative to
the all-ones weight of a chain. The statement is uniform in the width. -/
theorem exists_binary_rep_all_ones_add_tiny
    {L v : ℕ} (hL : 4 ≤ L) (hv : 0 < v) (hsmall : v ≤ 2^(L-4)) :
    ∃ u, Supp L u ∧ val L u=2^L-1+v ∧ dsum L u+2 ≤ L := by
  obtain ⟨u,hs,hu,hdu⟩ := exists_rep_le (L-4) (v-1) (by omega)
  have hsL := supp_mono (by omega : L-4 ≤ L) hs
  obtain ⟨w,hws,hw,hwd⟩ := exists_binary_rep_add_two_top_coins (by omega : 0 < L) u hsL
  refine ⟨w,hws,?_,?_⟩
  · rw [hw,val_pad (by omega : L-4 ≤ L) hs,hu]
    have hp : 0 < 2^L := by positivity
    omega
  · rw [hwd,dsum_pad (by omega : L-4 ≤ L) hs]
    omega

/-- An exterior-column representation with zero pivot and a small
strict deficit in its shifted coordinate gives a full-length rival.
Two saved coins in the shifted arm pay for the doubled top coin at the
exterior boundary; no sparsity of the other coefficients is assumed. -/
theorem not_validTuple_of_tiny_exterior_column_collision
    {n : ℕ} {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (a j : β) (hja : j ≠ a) (hcap : n ≤ 2^(L a)-1+2^(L a)) (hLj : 4 ≤ L j)
    (t : ℕ) (p : β → ℕ) (hp : ∀ i, p i < 2^(L i))
    (hpa : p a=0) (hpj : p j < t) (ht : t-p j ≤ 2^(L j-4))
    (heq : (∑ i, p i • x i)=2^(L a) • x a+t • x j) : ¬ ValidTuple g := by
  classical
  let X := fun i ↦ 2^(L i)-1-p i+(if i=a then 2^(L a) else if i=j then t else 0)
  have hXa : X a=2^(L a)-1+2^(L a) := by simp [X,hpa]
  have hXj : X j=2^(L j)-1+(t-p j) := by
    simp only [X,if_neg hja,if_true]
    have := hp j
    omega
  have hrep : ∀ i, ∃ u, val (L i) u=X i ∧
      dsum (L i) u+(if i=j then 2 else 0) ≤ L i+(if i=a then 2 else 0) := by
    intro i
    by_cases hi : i=a
    · subst i
      obtain ⟨u,hs,hu,hdu⟩ := exists_rep_le (L a) (2^(L a)-1) (by
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

/-- An entire exponentially long initial column outside a genuine
supported boundary misses the full binary box. This strengthens the
previous single-boundary exclusion, at arbitrary arity. -/
theorem tiny_exterior_column_not_in_box_of_genuine_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdzero : (∑ i, d i • x i)=0)
    (a j : β) (hda : 0 < d a) (hdj : 0 < d j) (hja : j ≠ a) (hLj : 4 ≤ L j)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (t : ℕ) (ht : t < d j) (htiny : t ≤ 2^(L j-4))
    (p : β → ℕ) (hp : ∀ i, p i < 2^(L i)) :
    (∑ i, p i • x i) ≠ 2^(L a) • x a+t • x j := by
  classical
  intro heq
  have hpa := pivot_eq_zero_of_short_exterior_column_collision L hL hlong hwide
    g hg E x b hchain d hd ⟨a,hda⟩ hdzero a j hja t ht p hp heq
  have hpj := shifted_coordinate_lt_of_genuine_exterior_column_collision L hL hlong hwide
    g hg E x b hchain d hd hdzero a j hda hdj hja hgenuine t p hp heq
  have hcap : n ≤ 2^(L a)-1+2^(L a) := (hlong a).trans (Nat.le_add_left _ _)
  exact not_validTuple_of_tiny_exterior_column_collision L hL g E x b hchain a j hja hcap hLj
    t p hp hpa hpj ((Nat.sub_le t (p j)).trans htiny) heq hg

/-- The distinct missing column residues give an exponential slack
charge in the shifted arm length. All other corner sides remain in
the exact packing volume, without any all-odd or individual-unit premise. -/
theorem exterior_column_charged_box_card_bound_of_genuine_long_chain_forest
    {n : ℕ} {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hlong : ∀ i, n ≤ 2^(L i)) (hwide : 2*n ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdzero : (∑ i, d i • x i)=0)
    (a j : β) (hda : 0 < d a) (hdj : 0 < d j) (hja : j ≠ a) (hLj : 4 ≤ L j)
    (hgenuine : ∀ v, g v ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n+min (d j) (2^(L j-4)+1) ≤ Fintype.card G+∏ i, (2^(L i)-d i) := by
  classical
  let T := min (d j) (2^(L j-4)+1)
  let w : Fin T → G := fun t ↦ 2^(L a) • x a+t.val • x j
  have hT : T ≤ d j := min_le_left _ _
  have hi : Function.Injective w := by
    intro t u he
    have hh := seed_interval_injective_of_supported_other_long_forest_relation L hL hlong hwide
      g hg E x b hchain d hd hdzero a j hda hja
      (a₁ := ⟨t.val,(t.isLt.trans_le hT).trans (hd j)⟩)
      (a₂ := ⟨u.val,(u.isLt.trans_le hT).trans (hd j)⟩) (add_left_cancel he)
    exact Fin.ext (congrArg (fun z : Fin (2^(L j)) ↦ z.val) hh)
  let F := Finset.univ.image w
  have hc : F.card=T := by simp only [F,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]
  have havoid : ∀ z ∈ F, ∀ p : β → ℕ, (∀ i, p i < 2^(L i)) → (∑ i, p i • x i) ≠ z := by
    intro z hz p hp
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hz
    have htiny : t.val ≤ 2^(L j-4) := by
      have h1 := t.isLt
      have h2 : T ≤ 2^(L j-4)+1 := min_le_right _ _
      omega
    exact tiny_exterior_column_not_in_box_of_genuine_long_chain_forest L hL hlong hwide
      g hg E x b hchain d hd hdzero a j hda hdj hja hLj hgenuine
      t.val (t.isLt.trans_le hT) htiny p hp
  have hh := box_card_bound_with_avoided_set_of_valid_long_chain_forest L hL hlong hwide
    g hg E x b hchain d hd ⟨a,hda⟩ hdzero F havoid
  simpa only [hc,T] using hh

/-- Beyond this explicit base, doubling dominates the cubic volume
bound. The proof is induction, with no finite family enumeration. -/
theorem three_length_cube_le_exponential {m : ℕ} (hm : 23 ≤ m) :
    (3*m)^3 ≤ 2^(m-4) := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hstep : (3*(m+1))^3 ≤ 2*(3*m)^3 := by
      have h1 : 4*m^2 ≤ m*m^2 := Nat.mul_le_mul_right (m^2) (by omega)
      have h2 : 4*m ≤ m*m := Nat.mul_le_mul_right m (by omega)
      nlinarith
    have hexp : 2^(m+1-4)=2*2^(m-4) := by
      rw [show m+1-4=(m-4)+1 by omega,pow_succ']
    rw [hexp]
    exact hstep.trans (Nat.mul_le_mul_left 2 ih)

/-- Every valid three-chain forest with genuine endpoints and all
arms long has at least binary ambient cardinality once its total length
is at least 67. The largest arm supplies more missing column points
than the entire relation corner can contain. This consumes arbitrary
positive slack, all seed parities, and nonunit seeds. -/
theorem binary_card_bound_of_genuine_long_three_chain_forest
    {n : ℕ} (hn : 67 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b) :
    2^n ≤ Fintype.card G := by
  classical
  by_contra hnot
  obtain ⟨d,hd,hdpos,hdzero,_⟩ := exists_small_corner_relation_of_valid_subbinary_long_chain_forest
    L hL hlong g hg E x b hchain (by omega)
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hne : Finset.univ.Nonempty (α := β) := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ,hr]
    decide
  obtain ⟨j,_,hmax⟩ := Finset.exists_max_image Finset.univ L hne
  have hnL : n ≤ 3*L j := by
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi ↦ hmax i hi)
    simpa only [hsize,Finset.sum_const,Finset.card_univ,smul_eq_mul,hr] using hs
  have hLj : 23 ≤ L j := by omega
  have hcube : n^3 ≤ 2^(L j-4) :=
    (Nat.pow_le_pow_left hnL 3).trans (three_length_cube_le_exponential hLj)
  have hsmall := small_complement_of_zero_relation_of_valid_chain_forest L hL
    g hg E x b hchain d hd hdpos hdzero
  have hside : ∀ i, 2^(L i)-d i ≤ n := by
    intro i
    have hh := Finset.single_le_sum (f := fun i ↦ 2^(L i)-1-d i)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    have := hd i
    omega
  have hvol : (∏ i, (2^(L i)-d i)) ≤ n^3 := by
    have hh := Finset.prod_le_pow_card Finset.univ (fun i ↦ 2^(L i)-d i) n (fun i _ ↦ hside i)
    simpa only [Finset.card_univ,hr] using hh
  have hpow : 2^(L j)=16*2^(L j-4) := by
    rw [show L j=4+(L j-4) by omega,pow_add]
    norm_num
  have hn_cube : n ≤ n^3 := by
    have h1 : 1 ≤ n*n := by nlinarith
    have hh := Nat.mul_le_mul_left n h1
    nlinarith
  have hdjlarge : n^3 < d j := by
    have hh := hside j
    have hj := hd j
    have hsub := Nat.sub_add_cancel hj.le
    omega
  have hdj : 0 < d j := by omega
  obtain ⟨a₀,a₁,ha₀,ha₁,hne₀⟩ := exists_two_supported_coordinates_of_long_forest_zero_relation
    (by omega) (by omega : 3 ≤ Fintype.card β) L hL hlong g hg E x b hchain d hd hdpos hdzero
  have ha : ∃ a, 0 < d a ∧ j ≠ a := by
    by_cases he : j=a₀
    · exact ⟨a₁,ha₁,by rw [he]; exact Ne.symm hne₀⟩
    · exact ⟨a₀,ha₀,he⟩
  obtain ⟨a,hda,hja⟩ := ha
  have hwide := box_wide_of_three_le_long_chain_forest (by omega : 3 ≤ Fintype.card β) L hL hlong E
  have hh := exterior_column_charged_box_card_bound_of_genuine_long_chain_forest L hL hlong hwide
    g hg E x b hchain d hd hdzero a j hda hdj hja (by omega) (hgenuine a)
  have hcharge : n^3 < min (d j) (2^(L j-4)+1) := by omega
  omega

/-- Direct original G1 descent in every even stratum for the entire
long three-chain class in lengths at least 67. Genuine endpoints and
the exact escape count are derived from failure of half descent. -/
theorem admitsValidTuple_half_of_critical_large_long_three_chain_forest
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (L : A → ℕ) (hL : ∀ a, 0 < L a) (hlong : ∀ a, n+1 ≤ 2^(L a))
    (E : (Σ a : A, Fin (L a)) ≃ Fin (n+1)) (x : A → ZMod (2^(s+1)*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hend : ∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val) :
    AdmitsValidTuple n (2^s*q) := by
  classical
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,hgenuine⟩ := exact_three_genuine_escapes_of_critical_without_half
    hq g hg hc A hA b hclosed hnohalf
  have hr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
  have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
    intro a t
    have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
    rw [he]
    exact hgenuine a.val a.property t
  have hh := binary_card_bound_of_genuine_long_three_chain_forest (by omega) hr L hL hlong
    g hg E x b hchain hgen
  rw [ZMod.card] at hh
  have hbound : stratumBound (n+1) (s+1) ≤ 2^(n+1) := Nat.sub_le _ _
  omega

/-- The unrestricted original three-escape data now force a SHORT
arm in every dimension at least 67 if no half child exists. The actual
three chains, endpoints, two odd seeds, and joint span are preserved;
all long-chain positive-slack residuals in this range are consumed. -/
theorem exists_short_arm_of_critical_large_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 66 ≤ n)
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
      AddSubgroup.closure (Set.range x)=⊤ ∧ ∃ a, 2^(L a) < n+1 := by
  classical
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan⟩ :=
    exists_spanning_three_chain_forest_of_critical_without_half hq (by omega) g hg hc A hA b hclosed hnohalf
  refine ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,?_⟩
  by_contra hnot
  have hlong : ∀ a, n+1 ≤ 2^(L a) := by
    intro a
    by_contra h
    exact hnot ⟨a,by omega⟩
  exact hnohalf (admitsValidTuple_half_of_critical_large_long_three_chain_forest hq hn g hg hc
    A hA b hclosed L hL hlong E x hchain hend)

end MinModulus
