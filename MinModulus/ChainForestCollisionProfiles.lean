import MinModulus.ChainForestTrimmedPacking

/-! Bounded small collision profiles in arbitrary-arm forests.
The joint-distance collision law separates high and low box points.
Small profiles with the same overflow pattern coincide; overflow can
occur only in short arms. This replaces an unstructured short-arm
collision family by at most four actual profiles for three chains in
lengths at least ten. The sharp global conjecture remains open. -/

namespace MinModulus
open Finset

/-- High-weight box points are injective at arbitrary arm lengths.
A collision would have one endpoint of total weight strictly below n. -/
theorem high_box_injective_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (p q : β → ℕ) (hp : ∀ i, p i < 2^(L i)) (hq : ∀ i, q i < 2^(L i))
    (hps : n ≤ ∑ i, p i) (hqs : n ≤ ∑ i, q i)
    (he : (∑ i, p i • x i)=∑ i, q i • x i) : p=q := by
  by_contra hne
  rcases box_collision_joint_distance_lt_of_valid_chain_forest L hL g hg E x b hchain
    p q hp hq hne he with h | h <;> omega

/-- Complementing a box point exchanges its top distance and weight. -/
theorem forest_box_weight_add_distance
    {β : Type*} [Fintype β] (L p : β → ℕ) (hp : ∀ i, p i < 2^(L i)) :
    (∑ i, (2^(L i)-1-p i))+(∑ i, p i)=∑ i, (2^(L i)-1) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.sub_add_cancel (by have := hp i; omega)

/-- When the box diameter is at least 2n-1, its low-weight points
are injective too. Thus any repeated value has only one low endpoint. -/
theorem low_box_injective_of_valid_wide_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (p q : β → ℕ) (hp : ∀ i, p i < 2^(L i)) (hq : ∀ i, q i < 2^(L i))
    (hps : (∑ i, p i) < n) (hqs : (∑ i, q i) < n)
    (he : (∑ i, p i • x i)=∑ i, q i • x i) : p=q := by
  have hpdist := forest_box_weight_add_distance L p hp
  have hqdist := forest_box_weight_add_distance L q hq
  by_contra hne
  rcases box_collision_joint_distance_lt_of_valid_chain_forest L hL g hg E x b hchain
    p q hp hq hne he with h | h <;> omega

/-- The ordinary binary-box fibre at a group element. -/
noncomputable def forestBoxFibre
    {β : Type*} [Fintype β] {G : Type*} [AddCommGroup G]
    (L : β → ℕ) (x : β → G) (z : G) : Finset (∀ i, Fin (2^(L i))) := by
  classical
  exact Finset.univ.filter (fun p ↦ (∑ i, (p i).val • x i)=z)

/-- Every fibre of a sufficiently wide actual forest box has at
most two points, including forests with short arms and mixed relations. -/
theorem box_fibre_card_le_two_of_valid_wide_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) (z : G) :
    (forestBoxFibre L x z).card ≤ 2 := by
  classical
  let F := Finset.univ.filter (fun p : ∀ i, Fin (2^(L i)) ↦ (∑ i, (p i).val • x i)=z)
  let low : F → Bool := fun p ↦ decide ((∑ i, (p.val i).val) < n)
  have hi : Function.Injective low := by
    intro p q he
    have hval : (∑ i, (p.val i).val • x i)=∑ i, (q.val i).val • x i :=
      (Finset.mem_filter.mp p.property).2.trans (Finset.mem_filter.mp q.property).2.symm
    have hs : ((∑ i, (p.val i).val) < n) ↔ ((∑ i, (q.val i).val) < n) := by
      simpa only [low,decide_eq_decide] using he
    have heq : (fun i ↦ (p.val i).val)=(fun i ↦ (q.val i).val) := by
      by_cases hp : (∑ i, (p.val i).val) < n
      · exact low_box_injective_of_valid_wide_chain_forest L hL hwide g hg E x b hchain
          _ _ (fun i ↦ (p.val i).isLt) (fun i ↦ (q.val i).isLt) hp (hs.mp hp) hval
      · have hq : ¬ (∑ i, (q.val i).val) < n := fun h ↦ hp (hs.mpr h)
        exact high_box_injective_of_valid_chain_forest L hL g hg E x b hchain
          _ _ (fun i ↦ (p.val i).isLt) (fun i ↦ (q.val i).isLt) (by omega) (by omega) hval
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun heq i)
  have hh := Fintype.card_le_of_injective low hi
  simpa only [Fintype.card_coe,Fintype.card_bool,F,forestBoxFibre] using hh

/-- Every bounded small representation of the distinguished forest
sum gives a real collision whenever the lower point lies in its
coordinate intervals. Its other endpoint has weight at least n. -/
theorem realize_small_forest_profile
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (x : β → G) (w q : β → ℕ)
    (hwsmall : (∑ i, w i) < n)
    (hweval : (∑ i, w i • x i)=∑ i, (2^(L i)-1) • x i)
    (hq : ∀ i, q i < 2^(L i))
    (hlo : ∀ i, w i ≤ 2^(L i)-1+q i) (hhi : ∀ i, q i ≤ w i) :
    ∃ p : β → ℕ, (∀ i, p i < 2^(L i)) ∧
      (∀ i, p i+w i=2^(L i)-1+q i) ∧ n ≤ (∑ i, p i) ∧
      (∑ i, p i • x i)=∑ i, q i • x i := by
  let p := fun i ↦ 2^(L i)-1+q i-w i
  have hp : ∀ i, p i < 2^(L i) := by
    intro i
    have := hq i
    have := hlo i
    have := hhi i
    dsimp only [p]
    omega
  have hidentity : ∀ i, p i+w i=2^(L i)-1+q i := fun i ↦ Nat.sub_add_cancel (hlo i)
  have hsum : (∑ i, p i)+(∑ i, w i)=(∑ i, (2^(L i)-1))+(∑ i, q i) := by
    simp only [← Finset.sum_add_distrib,hidentity]
  have hlarge : n ≤ ∑ i, p i := by omega
  refine ⟨p,hp,hidentity,hlarge,?_⟩
  have hgroup : (∑ i, p i • x i)+(∑ i, w i • x i)=
      (∑ i, (2^(L i)-1) • x i)+(∑ i, q i • x i) := by
    simp only [← Finset.sum_add_distrib,← add_nsmul,hidentity]
  rw [hweval] at hgroup
  exact add_right_cancel (by simpa only [add_comm (∑ i, (2^(L i)-1) • x i)] using hgroup)

/-- Two small profiles that admit the SAME lower box point coincide.
Their high endpoints have the same value and high-box injectivity applies. -/
theorem small_forest_profile_eq_of_common_lower_point
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w v q : β → ℕ) (hwsmall : (∑ i, w i) < n) (hvsmall : (∑ i, v i) < n)
    (hweval : (∑ i, w i • x i)=∑ i, (2^(L i)-1) • x i)
    (hveval : (∑ i, v i • x i)=∑ i, (2^(L i)-1) • x i)
    (hq : ∀ i, q i < 2^(L i))
    (hwl : ∀ i, w i ≤ 2^(L i)-1+q i) (hwh : ∀ i, q i ≤ w i)
    (hvl : ∀ i, v i ≤ 2^(L i)-1+q i) (hvh : ∀ i, q i ≤ v i) : w=v := by
  obtain ⟨p,hp,hip,hps,hpe⟩ := realize_small_forest_profile L hwide x w q hwsmall hweval hq hwl hwh
  obtain ⟨r,hr,hir,hrs,hre⟩ := realize_small_forest_profile L hwide x v q hvsmall hveval hq hvl hvh
  have he := high_box_injective_of_valid_chain_forest L hL g hg E x b hchain p r hp hr hps hrs (hpe.trans hre.symm)
  funext i
  have h1 := hip i
  have h2 := hir i
  have h3 := congrFun he i
  omega

/-- A small profile is uniquely determined by which coordinates
exceed their binary-box top. This is an actual relation classification,
not a finite census or a supplied relation-system hypothesis. -/
theorem small_forest_profile_eq_of_same_overflow
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w v : β → ℕ) (hw : ∀ i, w i ≤ 2*(2^(L i)-1)) (hv : ∀ i, v i ≤ 2*(2^(L i)-1))
    (hwsmall : (∑ i, w i) < n) (hvsmall : (∑ i, v i) < n)
    (hweval : (∑ i, w i • x i)=∑ i, (2^(L i)-1) • x i)
    (hveval : (∑ i, v i • x i)=∑ i, (2^(L i)-1) • x i)
    (hpattern : ∀ i, 2^(L i)-1 < w i ↔ 2^(L i)-1 < v i) : w=v := by
  classical
  let q := fun i ↦ if 2^(L i)-1 < w i then 2^(L i)-1 else 0
  have hq : ∀ i, q i < 2^(L i) := by
    intro i
    have hh : 0 < 2^(L i) := by positivity
    dsimp only [q]
    split_ifs <;> omega
  have hbounds : ∀ i, (w i ≤ 2^(L i)-1+q i ∧ q i ≤ w i) ∧
      (v i ≤ 2^(L i)-1+q i ∧ q i ≤ v i) := by
    intro i
    have hw' := hw i
    have hv' := hv i
    have hh := hpattern i
    dsimp only [q]
    split_ifs <;> omega
  exact small_forest_profile_eq_of_common_lower_point L hL hwide g hg E x b hchain
    w v q hwsmall hvsmall hweval hveval hq (fun i ↦ (hbounds i).1.1)
    (fun i ↦ (hbounds i).1.2) (fun i ↦ (hbounds i).2.1) (fun i ↦ (hbounds i).2.2)

/-- Bounded small representations of the distinguished forest sum.
The bound is exactly the range arising from two ordinary box points. -/
noncomputable def forestCollisionProfiles
    {β : Type*} [Fintype β] {G : Type*} [AddCommGroup G]
    (n : ℕ) (L : β → ℕ) (x : β → G) :
    Finset (∀ i, Fin (2*(2^(L i)-1)+1)) := by
  classical
  exact Finset.univ.filter (fun w ↦ (∑ i, (w i).val) < n ∧
    (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i)

/-- Overflow is possible only in an actually short arm. -/
theorem short_arm_of_small_profile_overflow
    {n : ℕ} {β : Type*} [Fintype β] (L w : β → ℕ)
    (hsmall : (∑ i, w i) < n) (i : β) (hi : 2^(L i)-1 < w i) : 2^(L i) < n := by
  have hh := Finset.single_le_sum (f := w) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- The entire actual profile family has at most 2^s elements,
where s is the NUMBER OF SHORT ARMS. No uniform arm-length bound is
assumed, and the original tuple and seed values determine every profile. -/
theorem forestCollisionProfiles_card_le_two_pow_short
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    (forestCollisionProfiles n L x).card ≤ 2^((Finset.univ.filter (fun i ↦ 2^(L i) < n)).card) := by
  classical
  let S := Finset.univ.filter (fun i ↦ 2^(L i) < n)
  let f : forestCollisionProfiles n L x → Finset S := fun w ↦
    Finset.univ.filter (fun i : S ↦ 2^(L i.val)-1 < (w.val i.val).val)
  have hi : Function.Injective f := by
    intro w v he
    have hw := (Finset.mem_filter.mp w.property).2
    have hv := (Finset.mem_filter.mp v.property).2
    have hpattern : ∀ i, 2^(L i)-1 < (w.val i).val ↔ 2^(L i)-1 < (v.val i).val := by
      intro i
      by_cases hs : i ∈ S
      · have hh : (⟨i,hs⟩ : S) ∈ f w ↔ (⟨i,hs⟩ : S) ∈ f v := by rw [he]
        simpa only [f,Finset.mem_filter,Finset.mem_univ,true_and] using hh
      · have hnshort : ¬ 2^(L i) < n := by simpa only [S,Finset.mem_filter,Finset.mem_univ,true_and] using hs
        have hw' : ¬ 2^(L i)-1 < (w.val i).val := fun h ↦ hnshort
          (short_arm_of_small_profile_overflow L _ hw.1 i h)
        have hv' : ¬ 2^(L i)-1 < (v.val i).val := fun h ↦ hnshort
          (short_arm_of_small_profile_overflow L _ hv.1 i h)
        simp only [hw',hv']
    have hh := small_forest_profile_eq_of_same_overflow L hL hwide g hg E x b hchain
      (fun i ↦ (w.val i).val) (fun i ↦ (v.val i).val)
      (fun i ↦ by have := (w.val i).isLt; omega) (fun i ↦ by have := (v.val i).isLt; omega)
      hw.1 hv.1 hw.2 hv.2 hpattern
    apply Subtype.ext
    funext i
    exact Fin.ext (congrFun hh i)
  have hh := Fintype.card_le_of_injective f hi
  simpa only [Fintype.card_coe,Fintype.card_finset,S] using hh

/-- A three-chain box already has the diameter needed for fibre
classification from total length seven onwards. -/
theorem three_chain_box_wide {n : ℕ} (hn : 7 ≤ n)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3) (L : β → ℕ) (hs : (∑ i, L i)=n) :
    2*n-1 ≤ ∑ i, (2^(L i)-1) := by
  classical
  have basic (l : ℕ) : 2*l ≤ 2^l := Nat.mul_le_pow (by decide) l
  have boost (l : ℕ) (hl : 3 ≤ l) : 2*l+2 ≤ 2^l := by
    induction l,hl using Nat.le_induction with
    | base => norm_num
    | succ l hl ih => rw [pow_succ]; nlinarith
  have hsome : ∃ i, 3 ≤ L i := by
    by_contra h
    simp only [not_exists,not_le] at h
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ show L i ≤ 2 by have := h i; omega)
    simp only [hs,Finset.sum_const,Finset.card_univ,hr,smul_eq_mul] at hh
    omega
  obtain ⟨j,hj⟩ := hsome
  have hh : ∀ i, 2*L i+(if i=j then 2 else 0) ≤ 2^(L i) := by
    intro i
    by_cases he : i=j
    · subst i; simpa using boost (L j) hj
    · simpa [he] using basic (L i)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hh i)
  simp only [Finset.sum_add_distrib,← Finset.mul_sum,hs] at hsum
  simp at hsum
  have hid : (∑ i, (2^(L i)-1))+3=∑ i, 2^(L i) := by
    have hpoint : ∀ i, (2^(L i)-1)+1=2^(L i) := by
      intro i
      have : 0 < 2^(L i) := by positivity
      omega
    have hh := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ ↦ hpoint i)
    simpa only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,hr,smul_eq_mul,mul_one] using hh
  omega

/-- Three chains of total length at least ten have at most two
short arms, where short means binary width strictly below total length. -/
theorem three_chain_short_arm_count_le_two {n : ℕ} (hn : 10 ≤ n)
    {β : Type*} [Fintype β] (hr : Fintype.card β=3) (L : β → ℕ) (hs : (∑ i, L i)=n) :
    (Finset.univ.filter (fun i ↦ 2^(L i) < n)).card ≤ 2 := by
  classical
  haveI : Nonempty β := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ L Finset.univ_nonempty
  have hnL : n ≤ 3*L j := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun i hi ↦ hj i hi)
    simpa only [hs,Finset.sum_const,Finset.card_univ,hr,smul_eq_mul] using h
  have hl : 4 ≤ L j := by omega
  have growth (l : ℕ) (hl : 4 ≤ l) : 3*l < 2^l := by
    induction l,hl using Nat.le_induction with
    | base => norm_num
    | succ l hl ih => rw [pow_succ]; nlinarith
  have hnshort : ¬ 2^(L j) < n := by have := growth (L j) hl; omega
  have hsub : Finset.univ.filter (fun i ↦ 2^(L i) < n) ⊆ Finset.univ.erase j := by
    intro i hi
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩
    intro he
    subst i
    exact hnshort (Finset.mem_filter.mp hi).2
  have hh := Finset.card_le_card hsub
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ j),Finset.card_univ,hr] using hh

/-- Every actual three-chain forest of length at least ten has
at most four bounded small collision profiles, with arbitrary arm lengths. -/
theorem forestCollisionProfiles_card_le_four_of_three_chains
    {n : ℕ} (hn : 10 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    (forestCollisionProfiles n L x).card ≤ 4 := by
  have hs : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hw := three_chain_box_wide (by omega : 7 ≤ n) hr L hs
  have hc := forestCollisionProfiles_card_le_two_pow_short L hL hw g hg E x b hchain
  have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (three_chain_short_arm_count_le_two hn hr L hs)
  exact hc.trans (by simpa using hh)

/-- The lower endpoints associated with one collision profile form
an explicit coordinate rectangle in the ordinary binary box. -/
noncomputable def forestProfileLowerBox
    {β : Type*} [Fintype β] (L : β → ℕ) (w : ∀ i, Fin (2*(2^(L i)-1)+1)) :
    Finset (∀ i, Fin (2^(L i))) := by
  classical
  exact Finset.univ.filter (fun q ↦ ∀ i,
    (w i).val ≤ 2^(L i)-1+(q i).val ∧ (q i).val ≤ (w i).val)

/-- Every actual ordinary-box collision is accounted for by one
of the small profiles and its lower rectangle. -/
theorem box_collision_meets_profile_lower_box
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (p q : ∀ i, Fin (2^(L i))) (hne : p ≠ q)
    (he : (∑ i, (p i).val • x i)=∑ i, (q i).val • x i) :
    ∃ w ∈ forestCollisionProfiles n L x,
      p ∈ forestProfileLowerBox L w ∨ q ∈ forestProfileLowerBox L w := by
  classical
  have oriented (p q : ∀ i, Fin (2^(L i)))
      (hs : (∑ i, (2^(L i)-1-(p i).val))+(∑ i, (q i).val) < n)
      (he : (∑ i, (p i).val • x i)=∑ i, (q i).val • x i) :
      ∃ w ∈ forestCollisionProfiles n L x, q ∈ forestProfileLowerBox L w := by
    let w : ∀ i, Fin (2*(2^(L i)-1)+1) := fun i ↦
      ⟨2^(L i)-1-(p i).val+(q i).val,by have := (p i).isLt; have := (q i).isLt; omega⟩
    have hid : ∀ i, (p i).val+(w i).val=2^(L i)-1+(q i).val := by
      intro i
      have := (p i).isLt
      dsimp only [w]
      omega
    have hwsmall : (∑ i, (w i).val)<n := by
      simpa only [w,Finset.sum_add_distrib] using hs
    have hgroup : (∑ i, (p i).val • x i)+(∑ i, (w i).val • x i)=
        (∑ i, (2^(L i)-1) • x i)+(∑ i, (q i).val • x i) := by
      simp only [← Finset.sum_add_distrib,← add_nsmul,hid]
    rw [he] at hgroup
    have hweval : (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i :=
      add_left_cancel (by simpa only [add_comm (∑ i, (2^(L i)-1) • x i)] using hgroup)
    refine ⟨w,?_,?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hwsmall,hweval⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,fun i ↦ ?_⟩
      have := (p i).isLt
      dsimp only [w]
      omega
  have hvalues : (fun i ↦ (p i).val) ≠ (fun i ↦ (q i).val) := by
    intro h
    apply hne
    funext i
    exact Fin.ext (congrFun h i)
  rcases box_collision_joint_distance_lt_of_valid_chain_forest L hL g hg E x b hchain
    _ _ (fun i ↦ (p i).isLt) (fun i ↦ (q i).isLt) hvalues he with h | h
  · obtain ⟨w,hw,hq⟩ := oriented p q h he
    exact ⟨w,hw,Or.inr hq⟩
  · obtain ⟨w,hw,hp⟩ := oriented q p h he.symm
    exact ⟨w,hw,Or.inl hp⟩

/-- The exact volume of a profile's lower rectangle. Its ith side
has length min(w_i+1, 2*(K_i-1)+1-w_i). -/
theorem forestProfileLowerBox_card
    {β : Type*} [Fintype β] (L : β → ℕ) (w : ∀ i, Fin (2*(2^(L i)-1)+1)) :
    (forestProfileLowerBox L w).card =
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) := by
  classical
  let B := ∀ i, Fin (2^(L i))
  let C : B → Prop := fun q ↦ ∀ i,
    (w i).val ≤ 2^(L i)-1+(q i).val ∧ (q i).val ≤ (w i).val
  let S := fun i ↦ min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)
  let CE : {q : B // C q} ≃ (∀ i, Fin (S i)) :=
    { toFun := fun q i ↦ ⟨(q.val i).val-((w i).val-(2^(L i)-1)),by
        have := (q.val i).isLt
        have := (w i).isLt
        have := q.property i
        dsimp only [S]
        omega⟩
      invFun := fun p ↦ ⟨fun i ↦ ⟨(p i).val+((w i).val-(2^(L i)-1)),by
        have := (p i).isLt
        have := (w i).isLt
        have hpos : 0 < 2^(L i) := by positivity
        dsimp only [S] at *
        omega⟩,fun i ↦ by
          have := (p i).isLt
          have := (w i).isLt
          dsimp only [S] at *
          omega⟩
      left_inv := by
        intro q
        apply Subtype.ext
        funext i
        apply Fin.ext
        have := q.property i
        dsimp only
        omega
      right_inv := by
        intro p
        funext i
        apply Fin.ext
        exact Nat.add_sub_cancel_right _ _ }
  have he := Fintype.card_congr CE
  simpa only [Fintype.card_subtype,Fintype.card_pi,Fintype.card_fin,B,C,S,forestProfileLowerBox] using he

/-- Distinct small profiles have disjoint lower rectangles in a
sufficiently wide actual valid forest. -/
theorem forestProfileLowerBox_disjoint_of_ne
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w v : ∀ i, Fin (2*(2^(L i)-1)+1))
    (hw : w ∈ forestCollisionProfiles n L x) (hv : v ∈ forestCollisionProfiles n L x)
    (hne : w ≠ v) : Disjoint (forestProfileLowerBox L w) (forestProfileLowerBox L v) := by
  classical
  apply Finset.disjoint_left.mpr
  intro q hq1 hq2
  have hw' := (Finset.mem_filter.mp hw).2
  have hv' := (Finset.mem_filter.mp hv).2
  have hq1' := (Finset.mem_filter.mp hq1).2
  have hq2' := (Finset.mem_filter.mp hq2).2
  have he := small_forest_profile_eq_of_common_lower_point L hL hwide g hg E x b hchain
    (fun i ↦ (w i).val) (fun i ↦ (v i).val) (fun i ↦ (q i).val)
    hw'.1 hv'.1 hw'.2 hv'.2 (fun i ↦ (q i).isLt)
    (fun i ↦ (hq1' i).1) (fun i ↦ (hq1' i).2) (fun i ↦ (hq2' i).1) (fun i ↦ (hq2' i).2)
  apply hne
  funext i
  exact Fin.ext (congrFun he i)

/-- A relation-sensitive packing bound: the entire binary deficit
is paid by the explicit rectangle volumes of actual small profiles.
At length at least ten, a three-chain forest has at most four summands. -/
theorem profile_volume_card_bound_of_valid_chain_forest
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    2^n ≤ Fintype.card G + ∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) := by
  classical
  let B := ∀ i, Fin (2^(L i))
  let U := (forestCollisionProfiles n L x).biUnion (forestProfileLowerBox L)
  let R := {p : B // p ∉ U}
  let f : R → G := fun p ↦ ∑ i, (p.val i).val • x i
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hbox : Fintype.card B=2^n := by
    rw [Fintype.card_pi]
    simp only [Fintype.card_fin]
    rw [Finset.prod_pow_eq_pow_sum,hsize]
  have hi : Function.Injective f := by
    intro p q he
    by_contra hne
    have hne' : p.val ≠ q.val := fun hh ↦ hne (Subtype.ext hh)
    obtain ⟨w,hw,hp | hq⟩ := box_collision_meets_profile_lower_box L hL g hg E x b hchain
      p.val q.val hne' he
    · exact p.property (Finset.mem_biUnion.mpr ⟨w,hw,hp⟩)
    · exact q.property (Finset.mem_biUnion.mpr ⟨w,hw,hq⟩)
  have hc : 2^n-U.card ≤ Fintype.card G := by
    have hh := Fintype.card_le_of_injective f hi
    simpa only [R,Fintype.card_subtype_compl,Fintype.card_coe,hbox] using hh
  have hU : U.card ≤ 2^n := by
    rw [← hbox]
    exact Finset.card_le_univ _
  have hvol : U.card ≤ ∑ w ∈ forestCollisionProfiles n L x,
      ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) := by
    have hh := Finset.card_biUnion_le (s := forestCollisionProfiles n L x) (t := forestProfileLowerBox L)
    simpa only [forestProfileLowerBox_card,U] using hh
  omega

/-- A subbinary actual forest must supply at least one genuine
small collision profile. This follows from the relation-sensitive packing. -/
theorem forestCollisionProfiles_nonempty_of_subbinary
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hsub : Fintype.card G < 2^n) : (forestCollisionProfiles n L x).Nonempty := by
  have hh := profile_volume_card_bound_of_valid_chain_forest L hL g hg E x b hchain
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty,add_zero] at hh
  omega

/-- The original three-escape no-half residual has between one
and four actual small profiles from length ten onwards. Their explicit
rectangle volumes pay its entire binary deficit. The forest, genuine
endpoints, odd seeds, and full joint span are extracted internally. -/
theorem exists_four_profile_forest_of_critical_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 9 ≤ n)
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
      (forestCollisionProfiles (n+1) L x).Nonempty ∧
      (forestCollisionProfiles (n+1) L x).card ≤ 4 ∧
      2^(s+1) ≤ 2^(n+1)-2^(s+1)*q ∧
      2^(n+1)-2^(s+1)*q ≤ ∑ w ∈ forestCollisionProfiles (n+1) L x,
        ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val) := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan⟩ :=
    exists_spanning_three_chain_forest_of_critical_without_half hq (by omega) g hg hc A hA b hclosed hnohalf
  have hr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
  have hsub : 2^(s+1)*q < 2^(n+1) := hc.trans_le (Nat.sub_le _ _)
  have hsub' : Fintype.card (ZMod (2^(s+1)*q)) < 2^(n+1) := by simpa only [ZMod.card] using hsub
  have hnonempty := forestCollisionProfiles_nonempty_of_subbinary L hL g hg E x b hchain hsub'
  have hfour := forestCollisionProfiles_card_le_four_of_three_chains (by omega) hr L hL g hg E x b hchain
  have hvol := profile_volume_card_bound_of_valid_chain_forest L hL g hg E x b hchain
  rw [ZMod.card] at hvol
  refine ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,hnonempty,hfour,
    two_pow_le_gap_of_subbinary_multiple hq.pos hsub,?_⟩
  omega

end MinModulus
