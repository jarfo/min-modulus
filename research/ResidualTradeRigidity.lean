import research.SingleRepeatFibres

set_option autoImplicit false
namespace MinModulus.Research
open Finset

/-- Within a repeated-sum fibre, the aggregate residual multiset identifies
the selected anchor subset, in every positive residual degree. -/
theorem residual_aggregate_determines_anchor_subset
    {n k : ℕ} {G : Type*} [AddCommGroup G]
    (hk : 0 < k) (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun z : G ↦ 2 • z))
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=k)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x)
    (I J : Finset (Fin n)) (hI : I ⊆ R) (hJ : J ⊆ R)
    (he : (∑ a ∈ I, (B a).val)=(∑ a ∈ J, (B a).val)) : I=J := by
  classical
  have hcard (U : Finset (Fin n)) (hU : U ⊆ R) :
      (∑ a ∈ U, (B a).val).card=U.card*k := by
    rw [Multiset.card_sum]
    calc
      _ = ∑ _ ∈ U, k := Finset.sum_congr rfl (fun a ha ↦ hc a (hU ha))
      _ = _ := by simp
  have hIJ : I.card=J.card := by
    have hh := congrArg Multiset.card he
    rw [hcard I hI,hcard J hJ] at hh
    exact Nat.eq_of_mul_eq_mul_right hk hh
  have eval (U : Finset (Fin n)) :
      ((∑ a ∈ U, (B a).val).map g).sum=∑ a ∈ U, ∑ i ∈ B a, g i := by
    induction U using Finset.induction_on with
    | empty => simp
    | @insert a U ha ih => simp [Finset.sum_insert ha,Multiset.map_add,ih]
  have hsum : (∑ a ∈ I, ∑ i ∈ B a, g i)=(∑ a ∈ J, ∑ i ∈ B a, g i) := by
    rw [← eval I,← eval J,he]
  have fibre (U : Finset (Fin n)) (hU : U ⊆ R) :
      2 • (∑ a ∈ U, g a)+(∑ a ∈ U, ∑ i ∈ B a, g i)=U.card • x := by
    calc
      _ = ∑ a ∈ U, (2 • g a+(∑ i ∈ B a, g i)) := by
        rw [Finset.sum_add_distrib,Finset.smul_sum]
      _ = ∑ _ ∈ U, x := Finset.sum_congr rfl (fun a ha ↦ hv a (hU ha))
      _ = _ := by simp
  have hdouble : 2 • (∑ a ∈ I, g a)=2 • (∑ a ∈ J, g a) := by
    apply add_right_cancel (b := ∑ a ∈ I, ∑ i ∈ B a, g i)
    rw [fibre I hI,hsum,fibre J hJ,hIJ]
  apply Finset.val_injective
  exact multiset_eq_finset_of_validTuple_card_sum g hg J I.val hIJ (hd hdouble)

/-- Two rooted residual balances in a quartic fibre cannot use disjoint
anchor sets. Odd residual cycles give such balances by alternating edges. -/
theorem quartic_rooted_residual_balances_share_anchor
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    (hd : Function.Injective (fun z : G ↦ 2 • z))
    (x : G) (R : Finset (Fin n)) (B : Fin n → Finset (Fin n))
    (hc : ∀ a ∈ R, (B a).card=2)
    (hv : ∀ a ∈ R, 2 • g a+(∑ i ∈ B a, g i)=x)
    (P Q U V : Finset (Fin n))
    (hP : P ⊆ R) (hQ : Q ⊆ R) (hU : U ⊆ R) (hV : V ⊆ R)
    (p q : Fin n) (hp : p ∉ R) (hq : q ∉ R)
    (he : (∑ a ∈ P, (B a).val)=(∑ a ∈ Q, (B a).val)+(p ::ₘ p ::ₘ 0))
    (hf : (∑ a ∈ U, (B a).val)=(∑ a ∈ V, (B a).val)+(q ::ₘ q ::ₘ 0)) :
    ¬ Disjoint (P ∪ Q) (U ∪ V) := by
  classical
  intro hdj
  have card (W : Finset (Fin n)) (hW : W ⊆ R) :
      (∑ a ∈ W, (B a).val).card=W.card*2 := by
    rw [Multiset.card_sum]
    calc
      _ = ∑ _ ∈ W, 2 := Finset.sum_congr rfl (fun a ha ↦ hc a (hW ha))
      _ = _ := by simp
  have hPQ : P.card=Q.card+1 := by
    have hh := congrArg Multiset.card he
    simp only [Multiset.card_add,Multiset.card_cons,Multiset.card_zero] at hh
    rw [card P hP,card Q hQ] at hh
    omega
  have hUV : U.card=V.card+1 := by
    have hh := congrArg Multiset.card hf
    simp only [Multiset.card_add,Multiset.card_cons,Multiset.card_zero] at hh
    rw [card U hU,card V hV] at hh
    omega
  have eval (W : Finset (Fin n)) :
      ((∑ a ∈ W, (B a).val).map g).sum=∑ a ∈ W, ∑ i ∈ B a, g i := by
    induction W using Finset.induction_on with
    | empty => simp
    | @insert a W ha ih => simp [Finset.sum_insert ha,Multiset.map_add,ih]
  have fibre (W : Finset (Fin n)) (hW : W ⊆ R) :
      2 • (∑ a ∈ W, g a)+(∑ a ∈ W, ∑ i ∈ B a, g i)=W.card • x := by
    calc
      _ = ∑ a ∈ W, (2 • g a+(∑ i ∈ B a, g i)) := by
        rw [Finset.sum_add_distrib,Finset.smul_sum]
      _ = ∑ _ ∈ W, x := Finset.sum_congr rfl (fun a ha ↦ hv a (hW ha))
      _ = _ := by simp
  have balance (A C : Finset (Fin n)) (hA : A ⊆ R) (hC : C ⊆ R)
      (r : Fin n) (hAC : A.card=C.card+1)
      (hh : (∑ a ∈ A, (B a).val)=(∑ a ∈ C, (B a).val)+(r ::ₘ r ::ₘ 0)) :
      2 • ((∑ a ∈ A, g a)+g r)=x+2 • (∑ a ∈ C, g a) := by
    have heval := congrArg (fun m : Multiset (Fin n) ↦ (m.map g).sum) hh
    simp only [Multiset.map_add,Multiset.sum_add,Multiset.map_cons,
      Multiset.sum_cons,Multiset.map_zero,Multiset.sum_zero,add_zero,eval] at heval
    have hfa := fibre A hA
    have hfc := fibre C hC
    rw [hAC,add_nsmul,one_nsmul,heval] at hfa
    rw [← hfc] at hfa
    apply add_right_cancel (b := ∑ a ∈ C, ∑ i ∈ B a, g i)
    calc
      _ = 2 • (∑ a ∈ A, g a)+((∑ a ∈ C, ∑ i ∈ B a, g i)+(g r+g r)) := by
        simp only [two_nsmul]; abel
      _ = (2 • (∑ a ∈ C, g a)+(∑ a ∈ C, ∑ i ∈ B a, g i))+x := hfa
      _ = _ := by abel
  have h1 := balance P Q hP hQ p hPQ he
  have h2 := balance U V hU hV q hUV hf
  have hs : (∑ a ∈ P, g a)+(∑ a ∈ V, g a)+g p=
      (∑ a ∈ Q, g a)+(∑ a ∈ U, g a)+g q := by
    apply hd
    calc
      _ = 2 • ((∑ a ∈ P, g a)+g p)+2 • (∑ a ∈ V, g a) := by abel
      _ = (x+2 • (∑ a ∈ Q, g a))+2 • (∑ a ∈ V, g a) := by rw [h1]
      _ = 2 • (∑ a ∈ Q, g a)+(x+2 • (∑ a ∈ V, g a)) := by abel
      _ = 2 • (∑ a ∈ Q, g a)+2 • ((∑ a ∈ U, g a)+g q) := by rw [h2]
      _ = _ := by abel
  have hPV : Disjoint P V := hdj.mono Finset.subset_union_left Finset.subset_union_right
  have hQU : Disjoint Q U := hdj.mono Finset.subset_union_right Finset.subset_union_left
  have hpPV : p ∉ P ∪ V := by
    intro hh
    exact hp (Finset.union_subset hP hV hh)
  have hqQU : q ∉ Q ∪ U := by
    intro hh
    exact hq (Finset.union_subset hQ hU hh)
  have hsame : insert p (P ∪ V)=insert q (Q ∪ U) := by
    apply Finset.val_injective
    apply multiset_eq_finset_of_validTuple_card_sum g hg (insert q (Q ∪ U)) _
    · change (insert p (P ∪ V)).card=(insert q (Q ∪ U)).card
      rw [Finset.card_insert_of_notMem hpPV,Finset.card_insert_of_notMem hqQU,
        Finset.card_union_of_disjoint hPV,Finset.card_union_of_disjoint hQU]
      omega
    · change (∑ a ∈ insert p (P ∪ V), g a)=(∑ a ∈ insert q (Q ∪ U), g a)
      rw [Finset.sum_insert hpPV,Finset.sum_insert hqQU,
        Finset.sum_union hPV,Finset.sum_union hQU]
      simpa only [add_comm (g p),add_comm (g q)] using hs
  have hsub : P ⊆ Q := by
    intro a ha
    have hmem : a ∈ insert q (Q ∪ U) := by rw [← hsame]; simp [ha]
    rcases Finset.mem_insert.mp hmem with h | h
    · subst a
      exact (hq (hP ha)).elim
    · rcases Finset.mem_union.mp h with h | h
      · exact h
      · exact (Finset.disjoint_left.mp hdj (Finset.mem_union_left Q ha)
          (Finset.mem_union_left V h)).elim
  have := Finset.card_le_card hsub
  omega

end MinModulus.Research
