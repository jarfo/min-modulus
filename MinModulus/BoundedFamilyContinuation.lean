import MinModulus.BoundedChainCorner

/-! Bounded-corner charge alone implies all original lower bounds for
arbitrary actual embedded chain families. Empty members can be removed;
maximal continuation retains the exact bounded-corner error. An internal
rejoin supplies a cycle whose joint outside weight gives the reflected-pair
budget. Thus the selected rejoining chain meets the doubled error allowance.
Global, exact-stratum and G3 consumers need no endpoint, width or separate
coverage premise. Binomial-charge corollaries follow. All unrestricted
conjecture gates remain open. -/

namespace MinModulus
open Finset
open scoped Classical

/-- Any subfamily's bounded corner embeds into the original corner by
putting zero on all omitted members. -/
theorem chain_family_corner_card_subtype_le
    {β : Type*} [Fintype β] {n : ℕ} (hn : 0 < n) (L : β → ℕ) (P : β → Prop) [DecidablePred P] :
    chainFamilyCornerCard n (fun i : {a : β // P a} ↦ L i.val) ≤ chainFamilyCornerCard n L := by
  classical
  letI : DecidableEq {a : β // P a} := Classical.decEq _
  let A := {a : β // P a}
  let C := {p : ∀ i : A, Fin (min n (2^(L i.val))) // (∑ i, (p i).val) < n}
  let D := {p : ∀ i : β, Fin (min n (2^(L i))) // (∑ i, (p i).val) < n}
  let lift (p : C) : ∀ a, Fin (min n (2^(L a))) := fun a ↦
    if ha : P a then p.val ⟨a,ha⟩ else ⟨0,lt_min hn (by positivity)⟩
  have hsum (p : C) : (∑ a, (lift p a).val)=(∑ i : A, (p.val i).val) := by
    have h := Fintype.sum_subtype_add_sum_subtype P (fun a ↦ (lift p a).val)
    have hleft : (∑ i : {a : β // P a}, (lift p i.val).val)=(∑ i : A, (p.val i).val) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [lift,dif_pos i.property]
    have hright : (∑ i : {a : β // ¬ P a}, (lift p i.val).val)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp only [lift,dif_neg i.property]
    rw [hleft,hright,add_zero] at h
    exact h.symm
  let f : C → D := fun p ↦ ⟨lift p,by rw [hsum]; exact p.property⟩
  have hf : Function.Injective f := by
    intro p q he
    apply Subtype.ext
    funext i
    have hh := congrArg (fun z : D ↦ z.val i.val) he
    simpa only [f,lift,dif_pos i.property] using hh
  have h := Fintype.card_le_of_injective f hf
  have hC : Fintype.card C=chainFamilyCornerCard n (fun i : {a : β // P a} ↦ L i.val) := by
    unfold chainFamilyCornerCard
    exact Fintype.card_congr (Equiv.refl _)
  have hD : Fintype.card D=chainFamilyCornerCard n L := by
    unfold chainFamilyCornerCard
    exact Fintype.card_congr (Equiv.refl _)
  rwa [hC,hD] at h

/-- The bounded-corner charge forces an actual continuation, even with empty members. -/
theorem exists_target_of_corner_family_below_binary
    {β : Type*} [Fintype β] {n N : ℕ} [NeZero N] (hn : 0 < n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyCornerError n L ≤ 2^(L a-3)) :
    ∃ w, g w=2 • g (v a (L a-1))+b := by
  classical
  let B := {i : β // 0 < L i}
  let M : B → ℕ := fun i ↦ L i.val
  let E : (Σ i, Fin (M i)) → Fin n := fun i ↦ v i.1.val i.2.val
  have hE : Function.Injective E := by
    rintro ⟨a,i⟩ ⟨c,j⟩ h
    obtain ⟨hac,hij⟩ := hv.2 a.val c.val i.val j.val i.isLt j.isLt h
    have hac' : a=c := Subtype.ext hac
    subst c
    have hi : i=j := Fin.ext hij
    subst j
    rfl
  have hsum : (∑ i : B, M i)=∑ i : β, L i := by
    have h := Fintype.sum_subtype_add_sum_subtype (fun i ↦ 0 < L i) L
    have hz : (∑ i : {i : β // ¬ 0 < L i}, L i.val)=0 := by
      apply Finset.sum_eq_zero
      intro i _
      have := i.property
      omega
    rw [hz,add_zero] at h
    exact h
  have hcard : chainFamilyCornerCard n M ≤ chainFamilyCornerCard n L :=
    chain_family_corner_card_subtype_le hn L (fun i ↦ 0 < L i)
  have hch : chainFamilyCornerError n M ≤ 2^(L a-3) := by
    apply le_trans ?_ hcharge
    unfold chainFamilyCornerError
    rw [hsum]
    exact Nat.mul_le_mul_right _ hcard
  by_contra hnone
  have hbound := binary_card_bound_of_partial_genuine_bounded_corner hn M (fun i ↦ i.property)
    g hg b (fun i : B ↦ x i.val) ⟨E,hE⟩ (fun i j ↦ hv.1 i.val j.val j.isLt)
    ⟨a,by omega⟩ ha hch (by intro w hw; exact hnone ⟨w,hw⟩)
  simp only [ZMod.card] at hbound
  omega

/-- The bounded-corner error is retained through maximal actual continuation. -/
theorem exists_corner_chain_family_internal_rejoin
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyCornerError n L ≤ 2^(L a-3)) :
    ∃ M : β → ℕ, ∃ V : β → ℕ → Fin n,
      ActualAffineChainFamily g b x M V ∧ L a ≤ M a ∧ (∑ c, L c) ≤ (∑ c, M c) ∧
        chainFamilyCornerError n M ≤ chainFamilyCornerError n L ∧
        ∃ i : ℕ, i < M a ∧ g (V a i)=2 • g (V a (M a-1))+b := by
  classical
  have hn : 0 < n := by have := (v a 0).isLt; omega
  have hwide := chain_family_width_of_corner_charge hn L a ha hcharge
  let P : ℕ → Prop := fun l ↦ ∃ M : β → ℕ, ∃ V : β → ℕ → Fin n,
    ActualAffineChainFamily g b x M V ∧ M a=l ∧ (∑ c, L c) ≤ (∑ c, M c) ∧
      chainFamilyCornerError n M ≤ chainFamilyCornerError n L
  let T := (Finset.range (n+1)).filter P
  have hlength (M : β → ℕ) (V : β → ℕ → Fin n)
      (hMV : ActualAffineChainFamily g b x M V) : M a ≤ n :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)).trans
      (actual_affine_chain_family_length_le g b x M V hMV)
  have hLa : L a ≤ n := hlength L v hv
  have haT : L a ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    ⟨L,v,hv,rfl,le_refl _,le_refl _⟩⟩
  obtain ⟨l,hlT,hmax⟩ := Finset.exists_max_image T id ⟨L a,haT⟩
  have hal : L a ≤ l := hmax (L a) haT
  obtain ⟨M,V,hMV,hMa,hcover,herr⟩ := (Finset.mem_filter.mp hlT).2
  have hwide' : 2*n+1 ≤ 2^(M a) := hwide.trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega))
  have hcharge' : chainFamilyCornerError n M ≤ 2^(M a-3) := by
    calc
      _ ≤ chainFamilyCornerError n L := herr
      _ ≤ 2^(L a-3) := hcharge
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)
  obtain ⟨w,hw⟩ := exists_target_of_corner_family_below_binary (by omega)
    g hg hsub b x M V hMV a (by omega) hcharge'
  have hown : ∃ i, i < M a ∧ V a i=w := by
    by_contra hh
    by_cases hother : ∃ c i, i < M c ∧ V c i=w
    · obtain ⟨c,i,hi,hci⟩ := hother
      have hac : a ≠ c := by
        intro heq
        subst c
        exact hh ⟨i,hi,hci⟩
      obtain ⟨MM,VV,hnew,hgrow,hsame,hothers⟩ := actual_affine_chain_family_splice_controlled g b x M V hMV a c hac
        (by omega) i hi (by rw [hci]; exact hw)
      have herrnew : chainFamilyCornerError n MM ≤ chainFamilyCornerError n L :=
        (chain_family_corner_error_mono M MM a (by omega) (by omega) hothers (by omega)).trans herr
      have hlen := hlength MM VV hnew
      have hmem : MM a ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        ⟨MM,VV,hnew,rfl,by omega,herrnew⟩⟩
      have hm := hmax (MM a) hmem
      change MM a ≤ l at hm
      omega
    · obtain ⟨MM,VV,hnew,hgrow,hmore,hothers⟩ := actual_affine_chain_family_extend_controlled g b x M V hMV a
        (by omega) w (by intro c i hi heq; exact hother ⟨c,i,hi,heq⟩) hw
      have herrnew : chainFamilyCornerError n MM ≤ chainFamilyCornerError n L :=
        (chain_family_corner_error_mono M MM a (by omega) (by omega) hothers (by omega)).trans herr
      have hlen := hlength MM VV hnew
      have hmem : MM a ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        ⟨MM,VV,hnew,rfl,by omega,herrnew⟩⟩
      have hm := hmax (MM a) hmem
      change MM a ≤ l at hm
      omega
  obtain ⟨i,hi,hwi⟩ := hown
  exact ⟨M,V,hMV,by omega,hcover,herr,i,hi,by rw [hwi]; exact hw⟩

/-- The actual cycle inside a rejoining member bounds the joint side
weight of every other member, supplying the reflected-pair budget. -/
theorem corner_reflection_budget_of_actual_family_rejoin
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b : ZMod N) (x : β → ZMod N) (M : β → ℕ) (V : β → ℕ → Fin n)
    (hMV : ActualAffineChainFamily g b x M V) (a : β) (ha : 0 < M a)
    (i : ℕ) (hi : i < M a) (hjoin : g (V a i)=2 • g (V a (M a-1))+b) :
    (∑ d, (min n (2^(M d))-1)) < 2*n := by
  classical
  let E (d : β) : Fin (M d) ↪ Fin n :=
    ⟨fun j ↦ V d j.val,by intro j k h; exact Fin.ext (hMV.2 d d j.val k.val j.isLt k.isLt h).2⟩
  have hpow (d : β) : ∀ j : Fin (M d), g (E d j)+b=2^j.val • x d := fun j ↦ hMV.1 d j.val j.isLt
  obtain ⟨c,hc,_,C,R,hC⟩ := exists_cycle_of_affine_chain_internal_rejoin ha
    (fun j ↦ g (E a j)) (validTuple_embedding (E a) g hg) b (x a) (Function.Embedding.refl _) (hpow a)
    ⟨⟨i,hi⟩,hjoin⟩
  let B := {d : β // d ≠ a}
  let D := Σ d : B, Fin (M d.val)
  let f : D ↪ Fin n := ⟨fun z ↦ V z.1.val z.2.val,by
    rintro ⟨d,j⟩ ⟨e,k⟩ he
    obtain ⟨hde,hjk⟩ := hMV.2 d.val e.val j.val k.val j.isLt k.isLt he
    have hd : d=e := Subtype.ext hde
    subst e
    exact Sigma.ext rfl (heq_of_eq (Fin.ext hjk))⟩
  let F : Fin c ↪ Fin n := C.trans (E a)
  have hdisj : ∀ j z, F j ≠ f z := by
    intro j z he
    have hh := (hMV.2 a z.1.val (C j).val z.2.val (C j).isLt z.2.isLt he).1
    exact z.1.property hh.symm
  have hweight := chain_family_weight_lt_of_disjoint_affine_cycle hc g hg b
    (fun d : B ↦ x d.val) (fun d : B ↦ M d.val) F f R hdisj hC
    (fun d j ↦ hMV.1 d.val j.val j.isLt)
  let A : Fin c ⊕ D → Fin n := Sum.elim F f
  have hA : Function.Injective A := by
    rintro (j | j) (k | k) he
    · exact congrArg Sum.inl (F.injective he)
    · exact (hdisj j k he).elim
    · exact (hdisj k j he.symm).elim
    · exact congrArg Sum.inr (f.injective he)
  have hsize : c+(∑ d : B, M d.val) ≤ n := by
    simpa only [D,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin] using
      Fintype.card_le_of_injective A hA
  have hother : (∑ d : B, (min n (2^(M d.val))-1)) < n := by
    apply lt_of_le_of_lt ?_ (hweight.trans_le hsize)
    exact Finset.sum_le_sum (fun d _ ↦ Nat.sub_le_sub_right (min_le_right n (2^(M d.val))) 1)
  letI : Unique {d : β // ¬ d ≠ a} :=
    { default := ⟨a,by simp⟩
      uniq := fun d ↦ Subtype.ext (by by_contra hh; exact d.property hh) }
  have hsingle : (∑ d : {d : β // ¬ d ≠ a}, (min n (2^(M d.val))-1)) ≤ n-1 := by
    calc
      _ ≤ (∑ _d : {d : β // ¬ d ≠ a}, (n-1)) := by
        apply Finset.sum_le_sum
        intro d _
        exact Nat.sub_le_sub_right (min_le_left n (2^(M d.val))) 1
      _ = _ := by simp
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun d ↦ d ≠ a) (fun d ↦ min n (2^(M d))-1)
  change (∑ d : {d : β // d ≠ a}, (min n (2^(M d.val))-1)) < n at hother
  omega

/-- A bounded-corner charge yields an actual internally rejoining
chain with the doubled scalar allowance below binary modulus. -/
theorem exists_rejoining_chain_of_bounded_corner_charge
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyCornerError n L ≤ 2^(L a-3)) :
    ∃ p : ℕ, ∃ hp : L a ≤ p, ∃ e : Fin p ↪ Fin n,
      (∀ i, g (e i)+b=2^i.val • x a) ∧
      (∃ i, g (e i)=2 • g (e ⟨p-1,by omega⟩)+b) ∧ n*2^(n-p) ≤ 2^(p-2) := by
  obtain ⟨M,V,hMV,hgrow,_,herr,i,hi,hjoin⟩ :=
    exists_corner_chain_family_internal_rejoin g hg hsub b x L v hv a ha hcharge
  have hn : 0 < n := by have := (V a 0).isLt; omega
  have hwide := chain_family_width_of_corner_charge hn L a ha hcharge
  have hwide' : n ≤ 2^(M a) := (by omega : n ≤ 2^(L a)).trans
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hgrow)
  have heq := truncated_family_error_eq_single_charge_of_rejoin g hg b x M V hMV a (by omega) hwide' i hi hjoin
  have hbudget := corner_reflection_budget_of_actual_family_rejoin g hg b x M V hMV a (by omega) i hi hjoin
  have hrect := truncated_error_le_twice_corner_error n M hbudget
  let E : Fin (M a) ↪ Fin n :=
    ⟨fun j ↦ V a j.val,by intro j k h; exact Fin.ext (hMV.2 a a j.val k.val j.isLt k.isLt h).2⟩
  refine ⟨M a,hgrow,E,(fun j ↦ hMV.1 a j.val j.isLt),⟨⟨i,hi⟩,hjoin⟩,?_⟩
  calc
    _ = chainFamilyTruncatedError n M := heq.symm
    _ ≤ 2*chainFamilyCornerError n M := hrect
    _ ≤ 2*chainFamilyCornerError n L := Nat.mul_le_mul_left 2 herr
    _ ≤ 2*2^(L a-3) := Nat.mul_le_mul_left 2 hcharge
    _ ≤ 2*2^(M a-3) := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega))
    _ = _ := by rw [← pow_succ']; congr 1; omega

/-- Original global lower bound from the bounded-corner charge alone. -/
theorem global_lower_bound_of_bounded_corner_family
    {β : Type*} [Fintype β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyCornerError n L ≤ 2^(L a-3)) :
    globalBound n ≤ N := by
  classical
  by_cases hsub : N < 2^n
  · have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
    obtain ⟨v,hv⟩ := exists_actual_affine_chain_family_of_embedding hn g b x L e hchain
    obtain ⟨p,hp,E,hE,hjoin,hch⟩ := exists_rejoining_chain_of_bounded_corner_charge g hg hsub b x L v hv a ha hcharge
    exact global_lower_bound_of_rejoining_chain_with_double_charge (by omega) g hg b (x a) E hE hjoin hch
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Original stratum lower bound from the bounded-corner charge alone. -/
theorem stratum_lower_bound_of_bounded_corner_family
    {β : Type*} [Fintype β] {n s d : ℕ} (hd : Odd d)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g)
    (b : ZMod (2^s*d)) (x : β → ZMod (2^s*d)) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyCornerError n L ≤ 2^(L a-3)) :
    stratumBound n s ≤ 2^s*d := by
  classical
  letI : NeZero (2^s*d) := ⟨(mul_pos (by positivity) hd.pos).ne'⟩
  by_cases hsub : 2^s*d < 2^n
  · have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
    obtain ⟨v,hv⟩ := exists_actual_affine_chain_family_of_embedding hn g b x L e hchain
    obtain ⟨p,hp,E,hE,hjoin,hch⟩ := exists_rejoining_chain_of_bounded_corner_charge g hg hsub b x L v hv a ha hcharge
    exact stratum_lower_bound_of_rejoining_chain_with_double_charge hd (by omega) g hg b (x a) E hE hjoin hch
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Original not validTuple exceptional from the bounded-corner charge alone. -/
theorem not_validTuple_exceptional_of_bounded_corner_family
    {β : Type*} [Fintype β] {n : ℕ} (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b : ZMod (2*globalBound (n-1))) (x : β → ZMod (2*globalBound (n-1))) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : chainFamilyCornerError n L ≤ 2^(L a-3)) :
    ¬ ValidTuple g := by
  intro hg
  have han : L a ≤ n := by
    have h := Fintype.card_le_of_injective (fun i : Fin (L a) ↦ e ⟨a,i⟩)
      (by intro i j h; have hh := e.injective h; cases hh; rfl)
    simpa only [Fintype.card_fin] using h
  have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
  letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
  have hsmall := two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1)
    (by simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow)
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hsmall
  have h := global_lower_bound_of_bounded_corner_family g hg b x L e hchain a ha hcharge
  omega

/-- The binomial charge now suffices for an arbitrary-endpoint partial family. -/
theorem global_lower_bound_of_binomial_charged_chain_family
    {β : Type*} [Fintype β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : (n+Fintype.card β-1).choose (Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3)) :
    globalBound n ≤ N := by
  have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
  have hcorner : chainFamilyCornerError n L ≤
      (n+Fintype.card β-1).choose (Fintype.card β)*2^(n-∑ i, L i) :=
    Nat.mul_le_mul_right _ (chain_family_corner_card_le_binomial hn L)
  exact global_lower_bound_of_bounded_corner_family g hg b x L e hchain a ha (hcorner.trans hcharge)

/-- The binomial charge now suffices for an arbitrary-endpoint partial family. -/
theorem stratum_lower_bound_of_binomial_charged_chain_family
    {β : Type*} [Fintype β] {n s d : ℕ} (hd : Odd d)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g)
    (b : ZMod (2^s*d)) (x : β → ZMod (2^s*d)) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : (n+Fintype.card β-1).choose (Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3)) :
    stratumBound n s ≤ 2^s*d := by
  have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
  have hcorner : chainFamilyCornerError n L ≤
      (n+Fintype.card β-1).choose (Fintype.card β)*2^(n-∑ i, L i) :=
    Nat.mul_le_mul_right _ (chain_family_corner_card_le_binomial hn L)
  exact stratum_lower_bound_of_bounded_corner_family hd g hg b x L e hchain a ha (hcorner.trans hcharge)

/-- The binomial charge now suffices for an arbitrary-endpoint partial family. -/
theorem not_validTuple_exceptional_of_binomial_charged_chain_family
    {β : Type*} [Fintype β] {n : ℕ} (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b : ZMod (2*globalBound (n-1))) (x : β → ZMod (2*globalBound (n-1))) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : (n+Fintype.card β-1).choose (Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3)) :
    ¬ ValidTuple g := by
  have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
  have hcorner : chainFamilyCornerError n L ≤
      (n+Fintype.card β-1).choose (Fintype.card β)*2^(n-∑ i, L i) :=
    Nat.mul_le_mul_right _ (chain_family_corner_card_le_binomial hn L)
  exact not_validTuple_exceptional_of_bounded_corner_family hnpow g b x L e hchain a ha (hcorner.trans hcharge)

end MinModulus
