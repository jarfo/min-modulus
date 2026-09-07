import MinModulus.ChainForestProfileBias

/-! Reflected small profiles exceed the actual coin budget. Overflow
requires strictly more dyadic underflow sides. Three-chain profiles have
at most one overflow, whose excess and other sides are dyadic. The original
large three-escape residual has at most three profiles; the sharp global
conjecture remains open. -/

namespace MinModulus
open Finset

/-- Reflecting a small profile about the all-ones weight produces
an actual rival weight vector. Every representation of it must exceed
the original coin budget. This needs no all-long or box-diameter premise. -/
theorem reflected_profile_coin_budget_gt_length
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w : β → ℕ) (hw : ∀ i, w i ≤ 2*(2^(L i)-1))
    (hsmall : (∑ i, w i) < n)
    (hrel : (∑ i, w i • x i)=∑ i, (2^(L i)-1) • x i)
    (u : β → ℕ → ℕ) (hu : ∀ i, val (L i) (u i)=2*(2^(L i)-1)-w i) :
    n < ∑ i, dsum (L i) (u i) := by
  classical
  let X := fun i ↦ 2*(2^(L i)-1)-w i
  have hid : ∀ i, X i+w i=2*(2^(L i)-1) := fun i ↦ Nat.sub_add_cancel (hw i)
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have htop : n ≤ ∑ i, (2^(L i)-1) := by
    rw [← hsize]
    apply Finset.sum_le_sum
    intro i _
    have := Nat.lt_two_pow_self (n := L i)
    omega
  have hsum : (∑ i, X i)+(∑ i, w i)=2*(∑ i, (2^(L i)-1)) := by
    rw [← Finset.sum_add_distrib]
    simp only [hid,Finset.mul_sum]
  have hneq : ∃ i, X i ≠ 2^(L i)-1 := by
    by_contra hn
    push Not at hn
    have hh : (∑ i, X i)=∑ i, (2^(L i)-1) := Finset.sum_congr rfl (fun i _ ↦ hn i)
    omega
  have heval : (∑ i, X i • x i)=∑ i, (2^(L i)-1) • x i := by
    have hh : (∑ i, X i • x i)+(∑ i, w i • x i)=
        (∑ i, (2^(L i)-1) • x i)+(∑ i, (2^(L i)-1) • x i) := by
      simp only [← Finset.sum_add_distrib,← add_nsmul,hid,two_mul]
    rw [hrel] at hh
    exact add_right_cancel hh
  by_contra hnot
  exact not_validTuple_of_chain_forest_integer_weights L X g E x b hchain u hu
    (by omega) (by omega) hneq heval hg

/-- A reflected coordinate costs one less coin when the profile
exceeds its top, one more when below, and no extra coin at the top. -/
theorem exists_reflected_profile_representation
    {L w : ℕ} (hL : 0 < L) (hw : w ≤ 2*(2^L-1)) :
    ∃ u, val L u=2*(2^L-1)-w ∧
      dsum L u+(if 2^L-1 < w then 1 else 0) ≤ L+(if w < 2^L-1 then 1 else 0) := by
  rcases lt_trichotomy w (2^L-1) with h | h | h
  · obtain ⟨u,_,hu,hc⟩ := exists_binary_rep_all_ones_add_small hL
      (by have := Nat.two_pow_pos L; omega : 2^L-1-w < 2^L)
    refine ⟨u,hu.trans (by omega),?_⟩
    simpa only [if_pos h,if_neg (by omega : ¬ 2^L-1 < w),add_zero] using hc
  · obtain ⟨u,_,hu,hc⟩ := exists_rep_le L w (by have := Nat.two_pow_pos L; omega)
    refine ⟨u,hu.trans (by omega),?_⟩
    simpa only [if_neg (by omega : ¬ 2^L-1 < w),if_neg (by omega : ¬ w < 2^L-1),add_zero] using hc
  · obtain ⟨u,_,hu,hc⟩ := exists_rep_lt L (2*(2^L-1)-w) (by omega)
    refine ⟨u,hu,?_⟩
    simp only [if_pos h,if_neg (by omega : ¬ w < 2^L-1),add_zero]
    omega

/-- Every actual small profile has STRICTLY more coordinates
below their box top than above it. Equality would fit a reflected rival. -/
theorem profile_overflow_card_lt_underflow_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w : β → ℕ) (hw : ∀ i, w i ≤ 2*(2^(L i)-1))
    (hsmall : (∑ i, w i) < n)
    (hrel : (∑ i, w i • x i)=∑ i, (2^(L i)-1) • x i) :
    (Finset.univ.filter (fun i ↦ 2^(L i)-1 < w i)).card <
      (Finset.univ.filter (fun i ↦ w i < 2^(L i)-1)).card := by
  classical
  have hrep := fun i ↦ exists_reflected_profile_representation (hL i) (hw i)
  choose u hu hc using hrep
  have hcost := reflected_profile_coin_budget_gt_length L g hg E x b hchain w hw hsmall hrel u hu
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hc i)
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hO : (∑ i, if 2^(L i)-1 < w i then 1 else 0)=
      (Finset.univ.filter (fun i ↦ 2^(L i)-1 < w i)).card := by simp
  have hU : (∑ i, if w i < 2^(L i)-1 then 1 else 0)=
      (Finset.univ.filter (fun i ↦ w i < 2^(L i)-1)).card := by simp
  simp only [Finset.sum_add_distrib,hsize,hO,hU] at hs
  omega

/-- In a three-chain forest, an actual profile can overflow AT MOST
ONE arm, in every dimension. The double-overflow pattern is impossible. -/
theorem three_chain_profile_overflow_card_le_one
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w : β → ℕ) (hw : ∀ i, w i ≤ 2*(2^(L i)-1))
    (hsmall : (∑ i, w i) < n)
    (hrel : (∑ i, w i • x i)=∑ i, (2^(L i)-1) • x i) :
    (Finset.univ.filter (fun i ↦ 2^(L i)-1 < w i)).card ≤ 1 := by
  classical
  have hh := profile_overflow_card_lt_underflow_card L hL g hg E x b hchain w hw hsmall hrel
  have hd : Disjoint (Finset.univ.filter (fun i ↦ 2^(L i)-1 < w i))
      (Finset.univ.filter (fun i ↦ w i < 2^(L i)-1)) := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have := (Finset.mem_filter.mp hi).2
    have := (Finset.mem_filter.mp hj).2
    omega
  have hc := Finset.card_le_univ ((Finset.univ.filter (fun i ↦ 2^(L i)-1 < w i)) ∪
      (Finset.univ.filter (fun i ↦ w i < 2^(L i)-1)))
  rw [Finset.card_union_of_disjoint hd,hr] at hc
  omega

/-- Coordinates strictly below their top whose complementary side
is a power of two: these are precisely the possible extra-coin owners. -/
noncomputable def forestProfileDyadicUnderflow
    {β : Type*} [Fintype β] (L w : β → ℕ) : Finset β := by
  classical
  exact Finset.univ.filter (fun i ↦ w i < 2^(L i)-1 ∧ ∃ e, w i+1=2^e)

/-- Overflow must be paid by STRICTLY MORE dyadic underflow sides.
A non-power underflow side saves the extra reflection coin. -/
theorem profile_overflow_card_lt_dyadic_underflow_card
    {n : ℕ} {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w : β → ℕ) (hw : ∀ i, w i ≤ 2*(2^(L i)-1))
    (hsmall : (∑ i, w i) < n)
    (hrel : (∑ i, w i • x i)=∑ i, (2^(L i)-1) • x i) :
    (Finset.univ.filter (fun i ↦ 2^(L i)-1 < w i)).card < (forestProfileDyadicUnderflow L w).card := by
  classical
  let D := forestProfileDyadicUnderflow L w
  have hrep : ∀ i, ∃ u, val (L i) u=2*(2^(L i)-1)-w i ∧
      dsum (L i) u+(if 2^(L i)-1 < w i then 1 else 0) ≤ L i+(if i ∈ D then 1 else 0) := by
    intro i
    by_cases hbad : w i < 2^(L i)-1 ∧ ¬ ∃ e, w i+1=2^e
    · obtain ⟨u,_,hu,hc⟩ := exists_binary_rep_double_range_sub_nonpower (hL i)
        (by omega : 0 < w i+1) (by omega : w i+1 < 2^(L i)) hbad.2
      have hnot : i ∉ D := by simp only [D,forestProfileDyadicUnderflow,Finset.mem_filter,Finset.mem_univ,true_and]; tauto
      refine ⟨u,hu.trans (by omega),?_⟩
      simpa only [if_neg (by omega : ¬ 2^(L i)-1 < w i),if_neg hnot,add_zero] using hc
    · obtain ⟨u,hu,hc⟩ := exists_reflected_profile_representation (hL i) (hw i)
      have hiff : i ∈ D ↔ w i < 2^(L i)-1 := by
        simp only [D,forestProfileDyadicUnderflow,Finset.mem_filter,Finset.mem_univ,true_and]
        tauto
      refine ⟨u,hu,?_⟩
      simpa only [hiff] using hc
  choose u hu hc using hrep
  have hcost := reflected_profile_coin_budget_gt_length L g hg E x b hchain w hw hsmall hrel u hu
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hc i)
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hO : (∑ i, if 2^(L i)-1 < w i then 1 else 0)=
      (Finset.univ.filter (fun i ↦ 2^(L i)-1 < w i)).card := by simp
  have hD : (∑ i, if i ∈ D then 1 else 0)=D.card := by simp
  simp only [Finset.sum_add_distrib,hsize,hO,hD] at hs
  change _ < D.card
  omega

/-- If a three-chain profile overflows one arm, BOTH other arms
have strict dyadic sides. Equal-top and non-power sides cannot pay for it. -/
theorem dyadic_other_sides_of_three_chain_profile_overflow
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w : β → ℕ) (hw : ∀ i, w i ≤ 2*(2^(L i)-1))
    (hsmall : (∑ i, w i) < n)
    (hrel : (∑ i, w i • x i)=∑ i, (2^(L i)-1) • x i)
    (a : β) (ha : 2^(L a)-1 < w a) :
    ∀ i, i ≠ a → w i < 2^(L i)-1 ∧ ∃ e, w i+1=2^e := by
  classical
  have hh := profile_overflow_card_lt_dyadic_underflow_card L hL g hg E x b hchain w hw hsmall hrel
  have hpos : 0 < (Finset.univ.filter (fun i ↦ 2^(L i)-1 < w i)).card :=
    Finset.card_pos.mpr ⟨a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩⟩
  have hsub : forestProfileDyadicUnderflow L w ⊆ Finset.univ.erase a := by
    intro i hi
    have hi' := (Finset.mem_filter.mp hi).2
    exact Finset.mem_erase.mpr ⟨by rintro rfl; omega,Finset.mem_univ _⟩
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,hr]
    omega)
  intro i hia
  have hi : i ∈ forestProfileDyadicUnderflow L w := by
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hia,Finset.mem_univ _⟩
  exact (Finset.mem_filter.mp hi).2

/-- The excess beyond an overflowing three-chain width is itself
a power of two. A non-power would save a second coin and create a rival. -/
theorem dyadic_excess_of_three_chain_profile_overflow
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w : β → ℕ) (hw : ∀ i, w i ≤ 2*(2^(L i)-1))
    (hsmall : (∑ i, w i) < n)
    (hrel : (∑ i, w i • x i)=∑ i, (2^(L i)-1) • x i)
    (a : β) (ha : 2^(L a)-1 < w a) : ∃ e, w a+1=2^(L a)+2^e := by
  classical
  by_contra hnot
  let z := w a+1-2^(L a)
  have hz : 0 < z := by dsimp only [z]; omega
  have hzK : z < 2^(L a) := by have := hw a; dsimp only [z]; omega
  have hnp : ¬ ∃ e, z=2^e := by
    rintro ⟨e,he⟩
    apply hnot
    refine ⟨e,?_⟩
    dsimp only [z] at he
    omega
  have hLa : 2 ≤ L a := by
    by_contra h
    have hLa1 : L a=1 := by have := hL a; omega
    have hz1 : z=1 := by simp only [hLa1,pow_one] at hzK; omega
    exact hnp ⟨0,by simp only [hz1,pow_zero]⟩
  have hrep : ∀ i, ∃ u, val (L i) u=2*(2^(L i)-1)-w i ∧
      dsum (L i) u+(if i=a then 3 else 0) ≤ L i+1 := by
    intro i
    by_cases hi : i=a
    · subst i
      obtain ⟨u,_,hu,hc⟩ := exists_rep_compl (L a) z hzK hz.ne' hnp
      refine ⟨u,hu.trans (by have := hw a; dsimp only [z]; omega),?_⟩
      simp only [if_true]
      omega
    · obtain ⟨u,hu,hc⟩ := exists_reflected_profile_representation (hL i) (hw i)
      refine ⟨u,hu,?_⟩
      rw [if_neg hi,add_zero]
      split_ifs at hc <;> omega
  choose u hu hc using hrep
  have hcost := reflected_profile_coin_budget_gt_length L g hg E x b hchain w hw hsmall hrel u hu
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hc i)
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    Finset.sum_const,Finset.card_univ,hr,smul_eq_mul,hsize] at hs
  omega

/-- Every finite set of size at most one is encoded by an option. -/
theorem exists_option_toFinset_of_card_le_one
    {α : Type*} (S : Finset α) (hS : S.card ≤ 1) : ∃ o : Option α, o.toFinset=S := by
  classical
  rcases S.eq_empty_or_nonempty with h | ⟨a,ha⟩
  · exact ⟨none,by simp only [Option.toFinset_none,h]⟩
  · refine ⟨some a,?_⟩
    simp only [Option.toFinset_some]
    apply Finset.ext
    intro b
    constructor
    · intro hb
      have : b=a := Finset.mem_singleton.mp hb
      simpa only [this] using ha
    · intro hb
      exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hS b hb a ha)

/-- A wide three-chain forest has at most one profile for no overflow
and one for each short arm. The double-overflow pattern contributes none. -/
theorem forestCollisionProfiles_card_le_short_add_one_of_three_chains
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i) (hwide : 2*n-1 ≤ ∑ i, (2^(L i)-1))
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    (forestCollisionProfiles n L x).card ≤ (Finset.univ.filter (fun i ↦ 2^(L i) < n)).card+1 := by
  classical
  let S := Finset.univ.filter (fun i ↦ 2^(L i) < n)
  let f : forestCollisionProfiles n L x → Finset S := fun w ↦
    Finset.univ.filter (fun i : S ↦ 2^(L i.val)-1 < (w.val i.val).val)
  have hf : ∀ w, (f w).card ≤ 1 := by
    intro w
    have hw := (Finset.mem_filter.mp w.property).2
    have hc := three_chain_profile_overflow_card_le_one hr L hL g hg E x b hchain
      (fun i ↦ (w.val i).val) (fun i ↦ by have := (w.val i).isLt; omega) hw.1 hw.2
    apply Finset.card_le_one.mpr
    intro a ha c hc'
    apply Subtype.ext
    apply Finset.card_le_one.mp hc a.val _ c.val _
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp ha).2⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hc').2⟩
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
  have hex := fun w ↦ exists_option_toFinset_of_card_le_one (f w) (hf w)
  choose o ho using hex
  have hoi : Function.Injective o := by
    intro w v he
    apply hi
    rw [← ho w,← ho v,he]
  have hh := Fintype.card_le_of_injective o hoi
  simpa only [Fintype.card_coe,Fintype.card_option,S] using hh

/-- At total length at least ten, there are at most THREE actual
profiles in a three-chain forest, improving the previous four-pattern bound. -/
theorem forestCollisionProfiles_card_le_three_of_three_chains
    {n : ℕ} (hn : 10 ≤ n) {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    (forestCollisionProfiles n L x).card ≤ 3 := by
  have hs : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  have hc := forestCollisionProfiles_card_le_short_add_one_of_three_chains hr L hL
    (three_chain_box_wide (by omega) hr L hs) g hg E x b hchain
  have hshort := three_chain_short_arm_count_le_two hn hr L hs
  omega

/-- Original three-escape no-half data now have ONE to THREE
actual profiles. Every overflow has one dyadic excess and two strict
dyadic companion sides, while all previous parity and gap data remain. -/
theorem exists_three_dyadic_profile_forest_of_critical_three_escape_without_half
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
      (forestCollisionProfiles (n+1) L x).card ≤ 3 ∧
      2^(s+1) ≤ 2^(n+1)-2^(s+1)*q ∧
      (2^(n+1)-2^(s+1)*q ≤ ∑ w ∈ forestCollisionProfiles (n+1) L x,
        ∏ i, min ((w i).val+1) (2*(2^(L i)-1)+1-(w i).val)) ∧
      (∀ v : Bool, 2^s ≤ forestProfileParityMass (n+1) L x v) ∧
      ∀ w ∈ forestCollisionProfiles (n+1) L x,
        (Finset.univ.filter (fun i ↦ 2^(L i)-1 < (w i).val)).card ≤ 1 ∧
        ∀ a, 2^(L a)-1 < (w a).val →
          (∃ e, (w a).val+1=2^(L a)+2^e) ∧
          ∀ i, i ≠ a → (w i).val < 2^(L i)-1 ∧ ∃ e, (w i).val+1=2^e := by
  classical
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,hne,_,hgap,hvol,hparity⟩ :=
    exists_parity_profile_forest_of_critical_three_escape_without_half hq hn g hg hc A hA b hclosed hnohalf
  have hr : Fintype.card A=3 := by simpa only [Fintype.card_coe] using hcard
  have hthree := forestCollisionProfiles_card_le_three_of_three_chains (by omega) hr L hL g hg E x b hchain
  refine ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,hspan,hne,hthree,hgap,hvol,hparity,?_⟩
  intro w hw
  have hw' : (∑ i, (w i).val) < n+1 ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hbound : ∀ i, (w i).val ≤ 2*(2^(L i)-1) := fun i ↦ by have := (w i).isLt; omega
  refine ⟨three_chain_profile_overflow_card_le_one hr L hL g hg E x b hchain _ hbound hw'.1 hw'.2,?_⟩
  intro a ha
  exact ⟨dyadic_excess_of_three_chain_profile_overflow hr L hL g hg E x b hchain _ hbound hw'.1 hw'.2 a ha,
    dyadic_other_sides_of_three_chain_profile_overflow hr L hL g hg E x b hchain _ hbound hw'.1 hw'.2 a ha⟩

end MinModulus
