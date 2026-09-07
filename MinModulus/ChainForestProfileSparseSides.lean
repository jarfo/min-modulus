import MinModulus.ChainForestProfileStripMass

/-! Uniform complement savings force sparse shifted profile coordinates.
Every actual three-chain profile has a representation with at most five
binary powers across w_i+1. In the no-overflow case these are the actual
rectangle sides. The sharp unrestricted global conjecture remains open. -/

namespace MinModulus
open Finset

/-- A positive side needing more than three binary powers has width
at least four. This finite base supports the uniform complement induction. -/
theorem four_le_width_of_not_three_binary_powers
    {w s : ℕ} (hs0 : 0 < s) (hs : s < 2^w)
    (hp : ¬ ∃ e, s=2^e) (hp2 : ¬ ∃ e f, s=2^e+2^f)
    (hp3 : ¬ ∃ e f k, s=2^e+2^f+2^k) : 4 ≤ w := by
  by_contra hn
  have hh : 2^w ≤ 2^3 := Nat.pow_le_pow_right (by decide) (by omega)
  norm_num at hh
  have hc : s=1 ∨ s=2 ∨ s=3 ∨ s=4 ∨ s=5 ∨ s=6 ∨ s=7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hp ⟨0,rfl⟩
  · exact hp ⟨1,rfl⟩
  · exact hp2 ⟨1,0,rfl⟩
  · exact hp ⟨2,rfl⟩
  · exact hp2 ⟨2,0,rfl⟩
  · exact hp2 ⟨2,1,rfl⟩
  · exact hp3 ⟨2,1,0,rfl⟩

/-- A complement missing at least four binary digits saves four coins,
uniformly in the chain length. -/
theorem exists_rep_compl_not_three_binary_powers : ∀ w s : ℕ,
    s < 2^w → 0 < s → (¬ ∃ e, s=2^e) → (¬ ∃ e f, s=2^e+2^f) →
    (¬ ∃ e f k, s=2^e+2^f+2^k) →
    ∃ u, Supp w u ∧ val w u=2^w-1-s ∧ dsum w u ≤ w-4 := by
  intro w
  induction w with
  | zero => intro s hs; norm_num at hs; omega
  | succ w ih =>
    intro s hs hs0 hp hp2 hp3
    have h2 : 2^(w+1)=2*2^w := by rw [pow_succ']
    have hwp : 0 < 2^w := by positivity
    rcases Nat.even_or_odd s with ⟨q,hq⟩ | ⟨q,hq⟩
    · have hq0 : 0 < q := by omega
      have hqlt : q < 2^w := by omega
      have hqp : ¬ ∃ e, q=2^e := by
        rintro ⟨e,he⟩
        exact hp ⟨e+1,by rw [pow_succ]; omega⟩
      have hqp2 : ¬ ∃ e f, q=2^e+2^f := by
        rintro ⟨e,f,he⟩
        exact hp2 ⟨e+1,f+1,by rw [pow_succ,pow_succ]; omega⟩
      have hqp3 : ¬ ∃ e f k, q=2^e+2^f+2^k := by
        rintro ⟨e,f,k,he⟩
        exact hp3 ⟨e+1,f+1,k+1,by rw [pow_succ,pow_succ,pow_succ]; omega⟩
      have hw4 := four_le_width_of_not_three_binary_powers hq0 hqlt hqp hqp2 hqp3
      obtain ⟨u,hu,hv,hc⟩ := ih q hqlt hq0 hqp hqp2 hqp3
      refine ⟨shift 1 u,shift_supp hu,?_,?_⟩
      · rw [shift_val,hv]; omega
      · rw [shift_dsum]; omega
    · have hq0 : 0 < q := by
        by_contra hn
        exact hp ⟨0,by rw [pow_zero]; omega⟩
      have hqlt : q < 2^w := by omega
      have hqp : ¬ ∃ e, q=2^e := by
        rintro ⟨e,he⟩
        exact hp2 ⟨e+1,0,by rw [pow_succ,pow_zero]; omega⟩
      have hqp2 : ¬ ∃ e f, q=2^e+2^f := by
        rintro ⟨e,f,he⟩
        exact hp3 ⟨e+1,f+1,0,by rw [pow_succ,pow_succ,pow_zero]; omega⟩
      have hw3 := three_le_width_of_not_two_binary_powers hq0 hqlt hqp hqp2
      obtain ⟨u,hu,hv,hc⟩ := exists_rep_compl_not_two_binary_powers w q hqlt hq0 hqp hqp2
      refine ⟨shift 0 u,shift_supp hu,?_,?_⟩
      · rw [shift_val,hv]; omega
      · rw [shift_dsum]; omega

/-- Reflecting a side that needs more than three binary powers saves
two coins relative to the original chain budget. -/
theorem exists_reflected_rep_not_three_binary_powers
    {L w : ℕ} (hL : 0 < L) (hw : w < 2^L-1)
    (hp : ¬ ∃ e, w+1=2^e) (hp2 : ¬ ∃ e f, w+1=2^e+2^f)
    (hp3 : ¬ ∃ e f k, w+1=2^e+2^f+2^k) :
    ∃ u, val L u=2*(2^L-1)-w ∧ dsum L u+2 ≤ L := by
  have hside : w+1 < 2^L := by omega
  have hL4 := four_le_width_of_not_three_binary_powers (by omega : 0 < w+1) hside hp hp2 hp3
  obtain ⟨u,hu,hv,hc⟩ := exists_rep_compl_not_three_binary_powers L (w+1) hside (by omega) hp hp2 hp3
  obtain ⟨v,_,hval,hcost⟩ := exists_binary_rep_add_two_top_coins hL u hu
  refine ⟨v,?_,?_⟩
  · rw [hval,hv]; have := Nat.two_pow_pos L; omega
  · omega

/-- In an actual three-chain small profile, any coordinate at or below
its top has a side that is a sum of at most three binary powers. -/
theorem three_chain_underflow_side_eq_at_most_three_powers
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w : β → ℕ) (hw : ∀ i, w i ≤ 2*(2^(L i)-1))
    (hsmall : (∑ i, w i)<n)
    (hrel : (∑ i, w i • x i)=∑ i, (2^(L i)-1) • x i)
    (a : β) (ha : w a ≤ 2^(L a)-1) :
    (∃ e, w a+1=2^e) ∨ (∃ e f, w a+1=2^e+2^f) ∨
      ∃ e f k, w a+1=2^e+2^f+2^k := by
  classical
  by_contra hn
  have hp : ¬ ∃ e, w a+1=2^e := fun h ↦ hn (Or.inl h)
  have hp2 : ¬ ∃ e f, w a+1=2^e+2^f := fun h ↦ hn (Or.inr (Or.inl h))
  have hp3 : ¬ ∃ e f k, w a+1=2^e+2^f+2^k := fun h ↦ hn (Or.inr (Or.inr h))
  have hat : w a < 2^(L a)-1 := by
    by_contra hn
    exact hp ⟨L a,by have := Nat.two_pow_pos (L a); omega⟩
  have hrep : ∀ i, ∃ u, val (L i) u=2*(2^(L i)-1)-w i ∧
      dsum (L i) u+(if i=a then 3 else 0) ≤ L i+1 := by
    intro i
    by_cases hi : i=a
    · subst i
      obtain ⟨u,hu,hc⟩ := exists_reflected_rep_not_three_binary_powers (hL a) hat hp hp2 hp3
      exact ⟨u,hu,by simp only [if_true]; omega⟩
    · obtain ⟨u,hu,hc⟩ := exists_reflected_profile_representation (hL i) (hw i)
      refine ⟨u,hu,?_⟩
      simp only [if_neg hi]
      split_ifs at hc <;> omega
  choose u hu hc using hrep
  have hcost := reflected_profile_coin_budget_gt_length L g hg E x b hchain w hw hsmall hrel u hu
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hc i)
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    hsize,Finset.sum_const,Finset.card_univ,hr,smul_eq_mul,mul_one] at hs
  omega

/-- A reflected side needing more than two binary powers saves one coin
relative to its original chain budget. -/
theorem exists_reflected_rep_not_two_binary_powers
    {L w : ℕ} (hL : 0 < L) (hw : w < 2^L-1)
    (hp : ¬ ∃ e, w+1=2^e) (hp2 : ¬ ∃ e f, w+1=2^e+2^f) :
    ∃ u, val L u=2*(2^L-1)-w ∧ dsum L u+1 ≤ L := by
  have hside : w+1 < 2^L := by omega
  have hL3 := three_le_width_of_not_two_binary_powers (by omega : 0 < w+1) hside hp hp2
  obtain ⟨u,hu,hv,hc⟩ := exists_rep_compl_not_two_binary_powers L (w+1) hside (by omega) hp hp2
  obtain ⟨v,_,hval,hcost⟩ := exists_binary_rep_add_two_top_coins hL u hu
  refine ⟨v,?_,?_⟩
  · rw [hval,hv]; have := Nat.two_pow_pos L; omega
  · omega

/-- A coordinate that is not a strict dyadic underflow requires no
extra reflection coin. Overflow and equal-top coordinates are included. -/
theorem exists_reflected_rep_of_not_dyadic_underflow
    {L w : ℕ} (hL : 0 < L) (hw : w ≤ 2*(2^L-1))
    (hnot : ¬ (w < 2^L-1 ∧ ∃ e, w+1=2^e)) :
    ∃ u, val L u=2*(2^L-1)-w ∧ dsum L u ≤ L := by
  by_cases hs : w < 2^L-1
  · have hp : ¬ ∃ e, w+1=2^e := fun h ↦ hnot ⟨hs,h⟩
    obtain ⟨u,_,hu,hc⟩ := exists_binary_rep_double_range_sub_nonpower hL
      (by omega : 0 < w+1) (by omega : w+1 < 2^L) hp
    exact ⟨u,hu.trans (by have := Nat.two_pow_pos L; omega),hc⟩
  · obtain ⟨u,hu,hc⟩ := exists_reflected_profile_representation hL hw
    refine ⟨u,hu,?_⟩
    simp only [if_neg hs,add_zero] at hc
    split_ifs at hc <;> omega

/-- If one strict-underflow side needs three binary powers, BOTH other
coordinates are strict dyadic underflows. Otherwise their combined
reflection savings create a full-length rival. -/
theorem three_chain_other_sides_dyadic_of_not_two_powers
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w : β → ℕ) (hw : ∀ i, w i ≤ 2*(2^(L i)-1))
    (hsmall : (∑ i, w i)<n)
    (hrel : (∑ i, w i • x i)=∑ i, (2^(L i)-1) • x i)
    (a : β) (ha : w a < 2^(L a)-1)
    (hp : ¬ ∃ e, w a+1=2^e) (hp2 : ¬ ∃ e f, w a+1=2^e+2^f) :
    ∀ c, c ≠ a → w c < 2^(L c)-1 ∧ ∃ e, w c+1=2^e := by
  classical
  intro c hca
  by_contra hn
  have hrep : ∀ i, ∃ u, val (L i) u=2*(2^(L i)-1)-w i ∧
      dsum (L i) u+(if i=a then 2 else 0)+(if i=c then 1 else 0) ≤ L i+1 := by
    intro i
    by_cases hia : i=a
    · subst i
      obtain ⟨u,hu,hc⟩ := exists_reflected_rep_not_two_binary_powers (hL a) ha hp hp2
      exact ⟨u,hu,by simp only [if_true,if_neg (Ne.symm hca),add_zero]; omega⟩
    · by_cases hic : i=c
      · subst i
        obtain ⟨u,hu,hc⟩ := exists_reflected_rep_of_not_dyadic_underflow (hL c) (hw c) hn
        exact ⟨u,hu,by simp only [if_true,if_neg hca,add_zero]; omega⟩
      · obtain ⟨u,hu,hc⟩ := exists_reflected_profile_representation (hL i) (hw i)
        refine ⟨u,hu,?_⟩
        simp only [if_neg hia,if_neg hic,add_zero]
        split_ifs at hc <;> omega
  choose u hu hc using hrep
  have hcost := reflected_profile_coin_budget_gt_length L g hg E x b hchain w hw hsmall hrel u hu
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ hc i)
  have hsize : (∑ i, L i)=n := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true,
    hsize,Finset.sum_const,Finset.card_univ,hr,smul_eq_mul,mul_one] at hs
  omega

/-- Every actual three-chain profile has at most five binary powers
across its three shifted coordinates: one single power and two sides
of at most two powers, or one three-power side and two single powers.
For a no-overflow profile these shifted coordinates ARE its rectangle
sides. This holds in every dimension. -/
theorem three_chain_profile_sparse_side_classification
    {n : ℕ} {β : Type*} [Fintype β] (hr : Fintype.card β=3)
    (L : β → ℕ) (hL : ∀ i, 0 < L i)
    {G : Type*} [AddCommGroup G] (g : Fin n → G) (hg : ValidTuple g)
    (E : (Σ i : β, Fin (L i)) ≃ Fin n) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (w : ∀ i, Fin (2*(2^(L i)-1)+1)) (hw : w ∈ forestCollisionProfiles n L x) :
    (∃ a, (∃ e, (w a).val+1=2^e) ∧ ∀ i, i ≠ a →
      (∃ e, (w i).val+1=2^e) ∨ ∃ e f, (w i).val+1=2^e+2^f) ∨
    (∃ a, (∃ e f k, (w a).val+1=2^e+2^f+2^k) ∧
      ∀ i, i ≠ a → ∃ e, (w i).val+1=2^e) := by
  classical
  have hmem : (∑ i, (w i).val)<n ∧
      (∑ i, (w i).val • x i)=∑ i, (2^(L i)-1) • x i := by
    simpa only [forestCollisionProfiles,Finset.mem_filter,Finset.mem_univ,true_and] using hw
  have hbound : ∀ i, (w i).val ≤ 2*(2^(L i)-1) := fun i ↦ by have := (w i).isLt; omega
  by_cases hall : ∀ i, (∃ e, (w i).val+1=2^e) ∨ ∃ e f, (w i).val+1=2^e+2^f
  · left
    have hd := profile_overflow_card_lt_dyadic_underflow_card L hL g hg E x b hchain
      (fun i ↦ (w i).val) hbound hmem.1 hmem.2
    obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < (forestProfileDyadicUnderflow L (fun i ↦ (w i).val)).card)
    have ha' : (w a).val < 2^(L a)-1 ∧ ∃ e, (w a).val+1=2^e := by
      simpa only [forestProfileDyadicUnderflow,Finset.mem_filter,Finset.mem_univ,true_and] using ha
    exact ⟨a,ha'.2,fun i _ ↦ hall i⟩
  · obtain ⟨a,hna⟩ := not_forall.mp hall
    have hp : ¬ ∃ e, (w a).val+1=2^e := fun h ↦ hna (Or.inl h)
    have hp2 : ¬ ∃ e f, (w a).val+1=2^e+2^f := fun h ↦ hna (Or.inr h)
    have ha : (w a).val < 2^(L a)-1 := by
      by_contra hn
      by_cases he : (w a).val=2^(L a)-1
      · exact hp ⟨L a,by have := Nat.two_pow_pos (L a); omega⟩
      · obtain ⟨e,he⟩ := dyadic_excess_of_three_chain_profile_overflow hr L hL g hg E x b hchain
          (fun i ↦ (w i).val) hbound hmem.1 hmem.2 a (by omega)
        exact hp2 ⟨L a,e,he⟩
    have hs := three_chain_underflow_side_eq_at_most_three_powers hr L hL g hg E x b hchain
      (fun i ↦ (w i).val) hbound hmem.1 hmem.2 a ha.le
    have hthree : ∃ e f k, (w a).val+1=2^e+2^f+2^k := (hs.resolve_left hp).resolve_left hp2
    have hothers := three_chain_other_sides_dyadic_of_not_two_powers hr L hL g hg E x b hchain
      (fun i ↦ (w i).val) hbound hmem.1 hmem.2 a ha hp hp2
    exact Or.inr ⟨a,hthree,fun i hi ↦ (hothers i hi).2⟩

end MinModulus
