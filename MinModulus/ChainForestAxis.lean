import MinModulus.ChainForestParity

/-! The entire long-forest AXIS class satisfies the sharp GLOBAL bound.
The small side sum forces the axis width and corner volume to equal n,
so n is dyadic and all other sides are one. Genuine endpoints make the
bound strict. Subglobal actual G1 corners are therefore interior; high
exact-stratum axes also give direct half descent. Lower exact strata at
dyadic lengths, interior corners, short arms and global G1/G2/G3 remain open. -/

namespace MinModulus
open Finset

/-- A positive integer box with small total side length cannot have
a side at least n unless that side is exactly n and all others are one.
The resulting volume is exactly n, in arbitrary dimension. -/
theorem axis_corner_volume_of_small_side_sum
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (A : β → ℕ)
    (hA : ∀ i, 0 < A i) (hsum : (∑ i, A i) ≤ n+Fintype.card β-1)
    (a : β) (ha : n ≤ A a) :
    A a=n ∧ (∀ i, i ≠ a → A i=1) ∧ (∏ i, A i)=n := by
  classical
  have hsplit : (∑ i, (A i-1))+Fintype.card β=(∑ i, A i) := by
    calc
      _=∑ i, ((A i-1)+1) := by simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,smul_eq_mul,mul_one]
      _=_ := by
        apply Finset.sum_congr rfl
        intro i _
        exact Nat.sub_add_cancel (hA i)
  have hs : (∑ i, (A i-1)) ≤ n-1 := by omega
  have hsingle : A a-1 ≤ ∑ i, (A i-1) := Finset.single_le_sum (f := fun i ↦ A i-1)
    (fun i _ ↦ Nat.zero_le _) (Finset.mem_univ a)
  have hae : A a=n := by have := hA a; omega
  have hrest : ∀ i, i ≠ a → A i=1 := by
    intro i hi
    have hp : ({a,i} : Finset β) ⊆ Finset.univ := Finset.subset_univ _
    have hh := Finset.sum_le_sum_of_subset hp (f := fun i ↦ A i-1)
    rw [Finset.sum_pair (Ne.symm hi)] at hh
    have := hA i
    omega
  refine ⟨hae,hrest,?_⟩
  calc
    _=A a := Finset.prod_eq_single a (fun i _ hi ↦ hrest i hi) (fun ha ↦ (ha (Finset.mem_univ a)).elim)
    _=n := hae

/-- An actual zero-relation axis in a long forest collapses the
ENTIRE corner volume to the tuple length. That length must itself be
dyadic, and every other corner side is one. No parity or unit is assumed. -/
theorem axis_corner_shape_of_valid_long_chain_forest
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0) (a : β) (ha : d a=0) :
    2^(L a)=n ∧ (∀ i, i ≠ a → 2^(L i)-d i=1) ∧
      (∏ i, (2^(L i)-d i))=n := by
  have hs := corner_side_sum_le_length_add_roots_sub_one_of_valid_chain_forest L hL
    g hg E x b hchain d hd hdpos hdzero
  have hp : ∀ i, 0 < 2^(L i)-d i := fun i ↦ Nat.sub_pos_of_lt (hd i)
  have hh := axis_corner_volume_of_small_side_sum hn (fun i ↦ 2^(L i)-d i) hp hs a
    (by simpa only [ha,Nat.sub_zero] using hlong a)
  simpa only [ha,Nat.sub_zero] using hh

/-- Every valid long forest with an axis zero relation satisfies the
SHARP GLOBAL lower bound, in an arbitrary finite abelian group. This
closes the whole axis class, not just tight or small-slack instances. -/
theorem global_lower_bound_of_valid_long_chain_forest_axis
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (hr : 3 ≤ Fintype.card β)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0) (a : β) (ha : d a=0) :
    globalBound n ≤ Fintype.card G := by
  obtain ⟨hsize,_,hvol⟩ := axis_corner_shape_of_valid_long_chain_forest hn L hL hlong
    g hg E x b hchain d hd hdpos hdzero a ha
  have hwide := box_wide_of_three_le_long_chain_forest hr L hL hlong E
  have hh := box_card_bound_of_valid_long_chain_forest L hL hlong hwide
    g hg E x b hchain d hd hdpos hdzero
  rw [hvol] at hh
  have hlog : 2^(Nat.log 2 n)=n := by
    rw [← hsize,Nat.log_pow (by decide : 1 < 2)]
  unfold globalBound
  rw [hlog]
  omega

/-- Genuine long-forest endpoints make the axis bound STRICT.
Hence even equality in the sharp global bound forces a rejoin in this
class. The statement retains arbitrary arity and arbitrary finite groups. -/
theorem global_bound_lt_card_of_genuine_long_chain_forest_axis
    {n : ℕ} (hn : 2 ≤ n) {β : Type*} [Fintype β] (hr : 3 ≤ Fintype.card β)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hgenuine : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0) (a : β) (ha : d a=0) :
    globalBound n < Fintype.card G := by
  obtain ⟨hsize,_,hvol⟩ := axis_corner_shape_of_valid_long_chain_forest (by omega) L hL hlong
    g hg E x b hchain d hd hdpos hdzero a ha
  have hh := strict_box_card_bound_of_genuine_long_chain_forest hn hr L hL hlong
    g hg E x b hchain hgenuine d hd hdpos hdzero
  rw [hvol] at hh
  have hlog : 2^(Nat.log 2 n)=n := by
    rw [← hsize,Nat.log_pow (by decide : 1 < 2)]
  have hn2 : n ≤ 2^n := Nat.le_of_lt (Nat.lt_two_pow_self)
  unfold globalBound
  rw [hlog]
  omega

/-- Every bounded nonzero relation in a SUBGLOBAL long forest is
strictly interior. All axis cases are consumed by the sharp bound. -/
theorem positive_relation_of_subglobal_valid_long_chain_forest
    {n : ℕ} (hn : 0 < n) {β : Type*} [Fintype β] (hr : 3 ≤ Fintype.card β)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    {G : Type*} [AddCommGroup G] [Fintype G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hc : Fintype.card G < globalBound n)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0) : ∀ i, 0 < d i := by
  intro a
  by_contra hnot
  have ha : d a=0 := by omega
  have hh := global_lower_bound_of_valid_long_chain_forest_axis hn hr L hL hlong
    g hg E x b hchain d hd hdpos hdzero a ha
  omega

/-- At ANY non-dyadic tuple length, a long-forest zero relation is
strictly interior without any modulus bound or parity assumption. -/
theorem positive_relation_of_nondyadic_valid_long_chain_forest
    {n : ℕ} (hn : 0 < n) (hnd : ∀ e, n ≠ 2^e) {β : Type*} [Fintype β]
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hlong : ∀ i, n ≤ 2^(L i))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : β → ℕ) (hd : ∀ i, d i < 2^(L i)) (hdpos : ∃ i, 0 < d i)
    (hdzero : (∑ i, d i • x i)=0) : ∀ i, 0 < d i := by
  intro a
  by_contra hnot
  have ha : d a=0 := by omega
  have hh := axis_corner_shape_of_valid_long_chain_forest hn L hL hlong
    g hg E x b hchain d hd hdpos hdzero a ha
  exact hnd (L a) hh.1.symm

/-- Direct ORIGINAL-G1 half descent for EVERY long three-chain axis
in the high strata, where the exact threshold is the global envelope.
Lower strata at dyadic tuple lengths are not silently claimed closed. -/
theorem admitsValidTuple_half_of_critical_high_stratum_long_forest_axis
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1)) (hs : Nat.log 2 (n+1) ≤ s+1)
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (L : A → ℕ) (hL : ∀ a, 0 < L a) (hlong : ∀ a, n+1 ≤ 2^(L a))
    (E : (Σ a : A, Fin (L a)) ≃ Fin (n+1)) (x : A → ZMod (2^(s+1)*q))
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (d : A → ℕ) (hd : ∀ a, d a < 2^(L a)) (hdpos : ∃ a, 0 < d a)
    (hdzero : (∑ a, d a • x a)=0) (a : A) (ha : d a=0) :
    AdmitsValidTuple n (2^s*q) := by
  classical
  by_contra hnohalf
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,_⟩ := exact_three_genuine_escapes_of_critical_without_half hq g hg hc A hA b hclosed hnohalf
  have hr : 3 ≤ Fintype.card A := by simp only [Fintype.card_coe,hcard,le_refl]
  have hh := global_lower_bound_of_valid_long_chain_forest_axis (by omega) hr L hL hlong
    g hg E x b hchain d hd hdpos hdzero a ha
  rw [ZMod.card] at hh
  have he : stratumBound (n+1) (s+1)=globalBound (n+1) := by
    simp only [stratumBound,globalBound,min_eq_right hs]
  rw [he] at hc
  omega

/-- The original SUBGLOBAL three-escape residual now supplies a
short arm or a strictly INTERIOR corner, with every previous parity,
support and exact-order charge on those same actual data. All axis
corners are closed throughout the global counterexample region. -/
theorem exists_short_arm_or_interior_corner_of_subglobal_three_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcglobal : 2^(s+1)*q < globalBound (n+1))
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
      ((∃ a, 2^(L a) < n+1) ∨ ∃ d : A → ℕ, (∀ a, 0 < d a ∧ d a < 2^(L a)) ∧
        (∃ a, 0 < d a) ∧ (∑ a, d a • x a)=0 ∧ (∑ a, (2^(L a)-d a)) ≤ n+3 ∧
        (∃ a e, 2^(L a)-d a=2^e) ∧
        2^(n+1)+(Finset.univ.filter (fun a ↦ 0 < d a)).card ≤ 2^(s+1)*q+∏ a, (2^(L a)-d a) ∧
        (((2^(n+1) : ℕ) : ℤ)+2*((Finset.univ.filter (fun a ↦ 0 < d a)).card : ℤ) ≤
          ((2^(s+1)*q : ℕ) : ℤ)+((∏ a, (2^(L a)-d a) : ℕ) : ℤ)+
          ∏ a, (if Even (x a).val then ((2^(L a)-d a : ℕ) : ℤ) else if Even (2^(L a)-d a) then 0 else 1)) ∧
        (∀ D : ℕ, 0 < D → (∀ a, D ∣ d a) →
          addOrderOf (∑ a, (d a/D) • x a)=D ∧ D ∣ 2^(s+1)*q ∧
          D ∣ 2^(s+1)*q+(∏ a, (2^(L a)-d a))-2^(n+1) ∧
          max D (Finset.univ.filter (fun a ↦ 0 < d a)).card ≤
            2^(s+1)*q+(∏ a, (2^(L a)-d a))-2^(n+1))) := by
  classical
  have hle : globalBound (n+1) ≤ stratumBound (n+1) (s+1) := by
    unfold globalBound stratumBound
    exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by omega : 1 ≤ 2) (min_le_right _ _)) _
  have hc := hcglobal.trans_le hle
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan⟩ :=
    exists_spanning_three_chain_forest_of_critical_without_half hq hn g hg hc A hA b hclosed hnohalf
  obtain ⟨hinj,_⟩ := injective_and_acyclic_of_critical_three_escape_without_half hq hn g hg hc A hA b hclosed hnohalf
  refine ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,?_⟩
  by_cases hlong : ∀ a, n+1 ≤ 2^(L a)
  · right
    have hN : Fintype.card (ZMod (2^(s+1)*q)) < 2^(n+1) := by
      rw [ZMod.card]
      exact lt_of_lt_of_le hc (by unfold stratumBound; exact Nat.sub_le _ _)
    obtain ⟨d,hd,hpos,hzero,hcorner⟩ :=
      exists_small_corner_relation_of_valid_subbinary_long_chain_forest L hL hlong g hg E x b hchain hN
    have hAr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
    have hr : 3 ≤ Fintype.card A := by omega
    have hgen : ∀ a, ∀ t, g t ≠ 2 • g (E ⟨a,⟨L a-1,by have := hL a; omega⟩⟩)+b := by
      intro a t
      have he := hend a ⟨L a-1,by have := hL a; omega⟩ (by have := hL a; simp only; omega)
      rw [he]
      exact hgenuine a t
    have hp := support_charged_box_card_bound_of_genuine_long_chain_forest (by omega) hr
      L hL hlong g hg hinj E x b hchain hgen d hd hpos hzero
    rw [hAr] at hcorner
    rw [ZMod.card] at hp
    have hNeven : 2 ∣ 2^(s+1)*q := by rw [pow_succ',mul_assoc]; exact dvd_mul_right 2 _
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (Finset.univ.filter (fun a ↦ Odd (x a).val)).card)
    have ho : ∃ a, Odd (x a).val := ⟨a,(Finset.mem_filter.mp ha).2⟩
    have hparity := parity_charged_box_card_bound_of_genuine_long_chain_forest hNeven (by omega) hr L hL hlong
      g hg hinj E x b hchain hgen ho d hd hpos hzero
    have hinterior := positive_relation_of_subglobal_valid_long_chain_forest (by omega) hr L hL hlong
      g hg E x b hchain (by simpa only [ZMod.card] using hcglobal) d hd hpos hzero
    refine ⟨d,fun a ↦ ⟨hinterior a,hd a⟩,hpos,hzero,by omega,
      exists_power_corner_side_of_valid_chain_forest L hL g hg E x b hchain d hd hpos hzero,hp,hparity,?_⟩
    intro D hD hdiv
    exact common_factor_and_support_charged_forest_slack (by omega) hr L hL hlong
      g hg hinj E x b hchain hgen d hd hpos hzero hD hdiv
  · left
    simpa only [not_forall,not_le] using hlong

end MinModulus
