import MinModulus.TwoChainCoverCycle

/-! Arbitrarily many disjoint actual affine chains give the original
global and every exact-stratum lower bound once their combined cover
pays the continuation and majority budgets. Empty members are retained
through coverage-preserving extensions and suffix splices. A maximal
designated chain rejoins internally; its incoming tail and all other
members are logarithmic, leaving a majority cycle. For r>=2 equal
length-m chains, n+r*log2(n)+r+3 <= (r+1)*m is sufficient. Endpoints,
seeds and remaining coordinates are arbitrary. Direct original G3
exclusion is included; unrestricted G1/G2/G3 remain open. -/

namespace MinModulus
open Finset
open scoped Classical

/-- Indexed actual chains with empty members permitted. Only indices
below the member length are used; distinct such indices give distinct
original coordinates. This representation allows coverage-preserving
updates without assuming that every surviving prefix is nonempty. -/
def ActualAffineChainFamily {β : Type*} {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (b : G) (x : β → G) (L : β → ℕ) (v : β → ℕ → Fin n) : Prop :=
  (∀ a i, i < L a → g (v a i)+b=2^i • x a) ∧
    ∀ a c i j, i < L a → j < L c → v a i=v c j → a=c ∧ i=j

/-- Even with empty members, an actual family covers at most the
original coordinate count. -/
theorem actual_affine_chain_family_length_le
    {β : Type*} [Fintype β] {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (b : G) (x : β → G) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) : (∑ a, L a) ≤ n := by
  let E : (Σ a, Fin (L a)) → Fin n := fun i ↦ v i.1 i.2.val
  have hE : Function.Injective E := by
    rintro ⟨a,i⟩ ⟨c,j⟩ h
    obtain ⟨hac,hij⟩ := hv.2 a c i.val j.val i.isLt j.isLt h
    subst c
    have hi : i=j := Fin.ext hij
    subst j
    rfl
  simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_le_of_injective E hE

/-- Dropping empty members loses no coverage and only improves the
partial-family charge. A selected charged arm still has an actual target. -/
theorem exists_target_of_actual_affine_chain_family_below_binary
    {β : Type*} [Fintype β] {n N : ℕ} [NeZero N] (hn : 0 < n)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3)) :
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
  have hcard : Fintype.card B ≤ Fintype.card β := Fintype.card_subtype_le _
  have hch : n^(Fintype.card B)*2^(n-∑ i : B, M i) ≤ 2^(L a-3) := by
    rw [hsum]
    exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hcard)).trans hcharge
  exact exists_target_of_partial_chain_forest_below_binary hn M (fun i ↦ i.property)
    g hg hsub b (fun i : B ↦ x i.val) ⟨E,hE⟩ (fun i j ↦ hv.1 i.val j.val j.isLt)
    ⟨a,by omega⟩ ha hch

/-- A new target extends a designated member of an arbitrary family.
Every other member and seed is preserved, and coverage increases by one. -/
theorem actual_affine_chain_family_extend
    {β : Type*} [Fintype β] [DecidableEq β] {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (b : G) (x : β → G) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 0 < L a)
    (w : Fin n) (hnew : ∀ c i, i < L c → v c i ≠ w)
    (htarget : g w=2 • g (v a (L a-1))+b) :
    ∃ M : β → ℕ, ∃ V : β → ℕ → Fin n,
      ActualAffineChainFamily g b x M V ∧ M a=L a+1 ∧ (∑ c, M c)=(∑ c, L c)+1 := by
  classical
  let M := Function.update L a (L a+1)
  let V := Function.update v a (fun i ↦ if i < L a then v a i else w)
  have hcoord : ∀ c i, i < M c →
      (i < L c ∧ V c i=v c i) ∨ (c=a ∧ i=L a ∧ V c i=w) := by
    intro c i hi
    by_cases hca : c=a
    · subst c
      simp only [M,Function.update_self] at hi
      by_cases hil : i < L a
      · exact Or.inl ⟨hil,by simp [V,hil]⟩
      · exact Or.inr ⟨rfl,by omega,by simp [V,hil]⟩
    · exact Or.inl ⟨by simpa [M,hca] using hi,by simp [V,hca]⟩
  have hend : g w+b=2^(L a) • x a := by
    calc
      _=2 • (g (v a (L a-1))+b) := by rw [htarget]; simp only [two_nsmul]; abel
      _=2 • (2^(L a-1) • x a) := by rw [hv.1 a (L a-1) (by omega)]
      _=_ := by rw [← mul_smul,← pow_succ',Nat.sub_add_cancel ha]
  have hfamily : ActualAffineChainFamily g b x M V := by
    constructor
    · intro c i hi
      rcases hcoord c i hi with ⟨hil,hvci⟩ | ⟨rfl,rfl,hvci⟩
      · rw [hvci]; exact hv.1 c i hil
      · rw [hvci]; exact hend
    · intro c d i j hi hj heq
      rcases hcoord c i hi with ⟨hic,hci⟩ | ⟨rfl,rfl,hci⟩
      · rcases hcoord d j hj with ⟨hjd,hdj⟩ | ⟨rfl,rfl,hdj⟩
        · exact hv.2 c d i j hic hjd (by simpa only [hci,hdj] using heq)
        · exact (hnew c i hic (by simpa only [hci,hdj] using heq)).elim
      · rcases hcoord d j hj with ⟨hjd,hdj⟩ | ⟨rfl,rfl,hdj⟩
        · exact (hnew d j hjd (by simpa only [hci,hdj] using heq.symm)).elim
        · exact ⟨rfl,rfl⟩
  refine ⟨M,V,hfamily,by simp [M],?_⟩
  have hsum := Finset.sum_erase_add Finset.univ L (Finset.mem_univ a)
  dsimp only [M]
  rw [Finset.sum_update_of_mem (Finset.mem_univ a),Finset.sdiff_singleton_eq_erase]
  omega

/-- Splice another member's entire reached suffix onto the designated
member, retaining its prefix and every other member. Coverage and all
seeds are preserved, including when the retained prefix is empty. -/
theorem actual_affine_chain_family_splice
    {β : Type*} [Fintype β] [DecidableEq β] {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (b : G) (x : β → G) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a z : β) (haz : a ≠ z) (ha : 0 < L a)
    (j : ℕ) (hj : j < L z) (htarget : g (v z j)=2 • g (v a (L a-1))+b) :
    ∃ M : β → ℕ, ∃ V : β → ℕ → Fin n,
      ActualAffineChainFamily g b x M V ∧ L a < M a ∧ (∑ c, M c)=∑ c, L c := by
  classical
  let M := Function.update (Function.update L z j) a (L a+(L z-j))
  let src : β → ℕ → β × ℕ := fun c i ↦ if c=a ∧ L a ≤ i then (z,j+(i-L a)) else (c,i)
  let V : β → ℕ → Fin n := fun c i ↦ v (src c i).1 (src c i).2
  have hMa : M a=L a+(L z-j) := by simp [M]
  have hMz : M z=j := by simp [M,Ne.symm haz]
  have hbound : ∀ c i, i < M c → (src c i).2 < L (src c i).1 := by
    intro c i hi
    by_cases hs : c=a ∧ L a ≤ i
    · obtain ⟨hca,hli⟩ := hs
      subst c
      simp only [src,if_pos (show a=a ∧ L a ≤ i from ⟨rfl,hli⟩)]
      rw [hMa] at hi
      omega
    · simp only [src,if_neg hs]
      by_cases hca : c=a
      · subst c
        have hnot : ¬ L a ≤ i := fun hh ↦ hs ⟨rfl,hh⟩
        omega
      · by_cases hcz : c=z
        · subst c
          rw [hMz] at hi
          omega
        · simpa [M,hca,hcz] using hi
  have hsrc : ∀ c d i k, i < M c → k < M d → src c i=src d k → c=d ∧ i=k := by
    intro c d i k hi hk heq
    by_cases hs : c=a ∧ L a ≤ i
    · by_cases ht : d=a ∧ L a ≤ k
      · obtain ⟨hca,hli⟩ := hs
        subst c
        obtain ⟨hda,hlk⟩ := ht
        subst d
        simp only [src,if_pos (show a=a ∧ L a ≤ i from ⟨rfl,hli⟩),if_pos (show a=a ∧ L a ≤ k from ⟨rfl,hlk⟩)] at heq
        have hidx := congrArg Prod.snd heq
        change j+(i-L a)=j+(k-L a) at hidx
        exact ⟨rfl,by omega⟩
      · simp only [src,if_pos hs,if_neg ht] at heq
        have hd : z=d := congrArg Prod.fst heq
        subst d
        rw [hMz] at hk
        have hidx := congrArg Prod.snd heq
        change j+(i-L a)=k at hidx
        omega
    · by_cases ht : d=a ∧ L a ≤ k
      · simp only [src,if_neg hs,if_pos ht] at heq
        have hc : c=z := congrArg Prod.fst heq
        subst c
        rw [hMz] at hi
        have hidx := congrArg Prod.snd heq
        change i=j+(k-L a) at hidx
        omega
      · simp only [src,if_neg hs,if_neg ht] at heq
        exact ⟨congrArg Prod.fst heq,congrArg Prod.snd heq⟩
  have hjoin : 2^j • x z=2^(L a) • x a := by
    calc
      _=g (v z j)+b := (hv.1 z j hj).symm
      _=2 • (g (v a (L a-1))+b) := by rw [htarget]; simp only [two_nsmul]; abel
      _=2 • (2^(L a-1) • x a) := by rw [hv.1 a (L a-1) (by omega)]
      _=_ := by rw [← mul_smul,← pow_succ',Nat.sub_add_cancel ha]
  have hfamily : ActualAffineChainFamily g b x M V := by
    constructor
    · intro c i hi
      have hb := hbound c i hi
      by_cases hs : c=a ∧ L a ≤ i
      · obtain ⟨hca,hli⟩ := hs
        subst c
        have hsa : src a i=(z,j+(i-L a)) := by simp [src,hli]
        rw [hsa] at hb
        change g (v (src a i).1 (src a i).2)+b=2^i • x a
        rw [hsa]
        rw [hv.1 z (j+(i-L a)) hb,Nat.add_comm j (i-L a),pow_add,mul_smul,hjoin,
          ← mul_smul,← pow_add,Nat.sub_add_cancel hli]
      · simp only [src,if_neg hs] at hb
        simp only [V,src,if_neg hs]
        exact hv.1 c i hb
    · intro c d i k hi hk heq
      have hh := hv.2 (src c i).1 (src d k).1 (src c i).2 (src d k).2
        (hbound c i hi) (hbound d k hk) heq
      exact hsrc c d i k hi hk (Prod.ext hh.1 hh.2)
  refine ⟨M,V,hfamily,by rw [hMa]; omega,?_⟩
  have hupdate (f : β → ℕ) (c : β) (k : ℕ) :
      (∑ i, Function.update f c k i)+f c=(∑ i, f i)+k := by
    have hsum := Finset.sum_erase_add Finset.univ f (Finset.mem_univ c)
    rw [Finset.sum_update_of_mem (Finset.mem_univ c),Finset.sdiff_singleton_eq_erase]
    omega
  have h0 := hupdate L z j
  have h1 := hupdate (Function.update L z j) a (L a+(L z-j))
  change (∑ c, M c)+(Function.update L z j) a=(∑ c, Function.update L z j c)+(L a+(L z-j)) at h1
  rw [Function.update_of_ne haz] at h1
  omega

/-- Maximize one member while retaining the initial total coverage.
Every charged family reaches an internal rejoin: extension and suffix
splicing rule out every other location of the actual target. -/
theorem exists_actual_affine_chain_family_internal_rejoin
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3)) :
    ∃ M : β → ℕ, ∃ V : β → ℕ → Fin n,
      ActualAffineChainFamily g b x M V ∧ L a ≤ M a ∧ (∑ c, L c) ≤ (∑ c, M c) ∧
        ∃ i : ℕ, i < M a ∧ g (V a i)=2 • g (V a (M a-1))+b := by
  classical
  let P : ℕ → Prop := fun l ↦ ∃ M : β → ℕ, ∃ V : β → ℕ → Fin n,
    ActualAffineChainFamily g b x M V ∧ M a=l ∧ (∑ c, L c) ≤ (∑ c, M c)
  let T := (Finset.range (n+1)).filter P
  have hlength (M : β → ℕ) (V : β → ℕ → Fin n)
      (hMV : ActualAffineChainFamily g b x M V) : M a ≤ n :=
    (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ a)).trans
      (actual_affine_chain_family_length_le g b x M V hMV)
  have hLa : L a ≤ n := hlength L v hv
  have haT : L a ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    ⟨L,v,hv,rfl,le_refl _⟩⟩
  obtain ⟨l,hlT,hmax⟩ := Finset.exists_max_image T id ⟨L a,haT⟩
  have hal : L a ≤ l := hmax (L a) haT
  obtain ⟨M,V,hMV,hMa,hcover⟩ := (Finset.mem_filter.mp hlT).2
  have hcharge' : n^(Fintype.card β)*2^(n-∑ c, M c) ≤ 2^(M a-3) := by
    calc
      _ ≤ n^(Fintype.card β)*2^(n-∑ c, L c) := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega))
      _ ≤ 2^(L a-3) := hcharge
      _ ≤ _ := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)
  obtain ⟨w,hw⟩ := exists_target_of_actual_affine_chain_family_below_binary (by omega)
    g hg hsub b x M V hMV a (by omega) hcharge'
  have hown : ∃ i, i < M a ∧ V a i=w := by
    by_contra hh
    by_cases hother : ∃ c i, i < M c ∧ V c i=w
    · obtain ⟨c,i,hi,hci⟩ := hother
      have hac : a ≠ c := by
        intro heq
        subst c
        exact hh ⟨i,hi,hci⟩
      obtain ⟨MM,VV,hnew,hgrow,hsame⟩ := actual_affine_chain_family_splice g b x M V hMV a c hac
        (by omega) i hi (by rw [hci]; exact hw)
      have hlen := hlength MM VV hnew
      have hmem : MM a ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        ⟨MM,VV,hnew,rfl,by omega⟩⟩
      have hm := hmax (MM a) hmem
      change MM a ≤ l at hm
      omega
    · obtain ⟨MM,VV,hnew,hgrow,hmore⟩ := actual_affine_chain_family_extend g b x M V hMV a
        (by omega) w (by intro c i hi heq; exact hother ⟨c,i,hi,heq⟩) hw
      have hlen := hlength MM VV hnew
      have hmem : MM a ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
        ⟨MM,VV,hnew,rfl,by omega⟩⟩
      have hm := hmax (MM a) hmem
      change MM a ≤ l at hm
      omega
  obtain ⟨i,hi,hwi⟩ := hown
  exact ⟨M,V,hMV,by omega,hcover,i,hi,by rw [hwi]; exact hw⟩

/-- After maximal continuation, every other chain and the incoming
tail are logarithmic. Sufficient combined coverage leaves a majority
cycle, uniformly in the number of selected chains. -/
theorem exists_majority_cycle_of_actual_affine_chain_family
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g) (hsub : N < 2^n)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3))
    (hcover : n+2*(Fintype.card β)*Nat.log 2 n ≤ 2*(∑ i, L i)) :
    ∃ c : ℕ, 2 ≤ c ∧ n ≤ 2*c ∧ ∃ C : Fin c ↪ Fin n,
      ∃ R : Equiv.Perm (Fin c), ∀ i, g (C (R i))=2 • g (C i)+b := by
  classical
  obtain ⟨M,V,hMV,hgrow,hsize,i,hi,hjoin⟩ :=
    exists_actual_affine_chain_family_internal_rejoin g hg hsub b x L v hv a ha hcharge
  let E (d : β) : Fin (M d) ↪ Fin n :=
    ⟨fun j ↦ V d j.val,by intro j k h; exact Fin.ext (hMV.2 d d j.val k.val j.isLt k.isLt h).2⟩
  have hpow (d : β) : ∀ j : Fin (M d), g (E d j)+b=2^j.val • x d := fun j ↦ hMV.1 d j.val j.isLt
  obtain ⟨c,hc,hac,C,R,hC⟩ := exists_cycle_of_affine_chain_internal_rejoin (by omega : 0 < M a)
    (fun j ↦ g (E a j)) (validTuple_embedding (E a) g hg) b (x a) (Function.Embedding.refl _) (hpow a)
    ⟨⟨i,hi⟩,hjoin⟩
  have han : M a ≤ n := by simpa using Fintype.card_le_of_injective _ (E a).injective
  have hlog := Nat.log_mono_right (b := 2) han
  have hother : ∀ d, d ≠ a → M d ≤ Nat.log 2 n := by
    intro d hda
    apply logarithmic_chain_disjoint_from_affine_cycle hc g hg b (x d) (C.trans (E a)) (E d) R
    · intro j k heq
      have had := (hMV.2 a d (C j).val k.val (C j).isLt k.isLt heq).1
      exact hda had.symm
    · exact hC
    · exact hpow d
  have hsum : (∑ d ∈ Finset.univ.erase a, M d) ≤ (Fintype.card β-1)*Nat.log 2 n := by
    calc
      _ ≤ ∑ _d ∈ Finset.univ.erase a, Nat.log 2 n := Finset.sum_le_sum
        (fun d hd ↦ hother d (Finset.mem_erase.mp hd).1)
      _ = _ := by simp
  have hsplit := Finset.sum_erase_add Finset.univ M (Finset.mem_univ a)
  have hr : 1 ≤ Fintype.card β := Fintype.card_pos_iff.mpr ⟨a⟩
  have hmul : (Fintype.card β-1)*Nat.log 2 n+Nat.log 2 n=(Fintype.card β)*Nat.log 2 n := by
    calc
      _=((Fintype.card β-1)+1)*Nat.log 2 n := by ring
      _=_ := by rw [Nat.sub_add_cancel hr]
  have hcovered : (∑ d, L d) ≤ c+(Fintype.card β)*Nat.log 2 n := by omega
  have hmajor : n ≤ 2*c := by nlinarith
  exact ⟨c,by omega,hmajor,C.trans (E a),R,hC⟩

/-- Original global lower bound for an arbitrary actual chain family
whose combined cover pays the continuation and majority budgets. -/
theorem global_lower_bound_of_actual_affine_chain_family
    {β : Type*} [Fintype β] [DecidableEq β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3))
    (hcover : n+2*(Fintype.card β)*Nat.log 2 n ≤ 2*(∑ i, L i)) : globalBound n ≤ N := by
  by_cases hsub : N < 2^n
  · obtain ⟨c,hc,hmajor,C,R,hR⟩ := exists_majority_cycle_of_actual_affine_chain_family
      g hg hsub b x L v hv a ha hcharge hcover
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact global_lower_bound_of_valid_majority_affine_doubling_cycle hc (by omega) g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Every original exact-stratum bound for arbitrary actual families
at the same combined-cover thresholds. -/
theorem stratum_lower_bound_of_actual_affine_chain_family
    {β : Type*} [Fintype β] [DecidableEq β] {n s d : ℕ} (hd : Odd d)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g)
    (b : ZMod (2^s*d)) (x : β → ZMod (2^s*d)) (L : β → ℕ) (v : β → ℕ → Fin n)
    (hv : ActualAffineChainFamily g b x L v) (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3))
    (hcover : n+2*(Fintype.card β)*Nat.log 2 n ≤ 2*(∑ i, L i)) : stratumBound n s ≤ 2^s*d := by
  letI : NeZero (2^s*d) := ⟨(mul_pos (by positivity) hd.pos).ne'⟩
  by_cases hsub : 2^s*d < 2^n
  · obtain ⟨c,hc,hmajor,C,R,hR⟩ := exists_majority_cycle_of_actual_affine_chain_family
      g hg hsub b x L v hv a ha hcharge hcover
    have hcn : c ≤ n := by simpa using Fintype.card_le_of_injective _ C.injective
    obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hcn
    obtain ⟨P,hP⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) C
      (Fin.castAdd_injective c k) C.injective
    exact stratum_lower_bound_of_valid_majority_affine_doubling_cycle hc (by omega) hd g hg P b R
      (by simpa only [hP] using hR)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- An actual embedded family supplies the internal representation;
coordinates outside a member's stated length are never used. -/
theorem exists_actual_affine_chain_family_of_embedding
    {β : Type*} {n : ℕ} (hn : 0 < n) {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (b : G) (x : β → G) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a) :
    ∃ v : β → ℕ → Fin n, ActualAffineChainFamily g b x L v := by
  let v : β → ℕ → Fin n := fun a i ↦ if hi : i < L a then e ⟨a,⟨i,hi⟩⟩ else ⟨0,hn⟩
  refine ⟨v,?_,?_⟩
  · intro a i hi
    simpa only [v,dif_pos hi] using hchain a ⟨i,hi⟩
  · intro a c i j hi hj heq
    have hh : e ⟨a,⟨i,hi⟩⟩=e ⟨c,⟨j,hj⟩⟩ := by simpa only [v,dif_pos hi,dif_pos hj] using heq
    have h := e.injective hh
    exact ⟨congrArg Sigma.fst h,congrArg (fun z : Σ a, Fin (L a) ↦ z.2.val) h⟩

/-- Original global bound for arbitrary embedded partial affine chain
families, with unrestricted endpoints and remaining coordinates. -/
theorem global_lower_bound_of_embedded_affine_chain_family
    {β : Type*} [Fintype β] {n N : ℕ} [NeZero N]
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (b : ZMod N) (x : β → ZMod N) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3))
    (hcover : n+2*(Fintype.card β)*Nat.log 2 n ≤ 2*(∑ i, L i)) : globalBound n ≤ N := by
  classical
  have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
  obtain ⟨v,hv⟩ := exists_actual_affine_chain_family_of_embedding hn g b x L e hchain
  exact global_lower_bound_of_actual_affine_chain_family g hg b x L v hv a ha hcharge hcover

/-- Every exact stratum for the same arbitrary embedded families. -/
theorem stratum_lower_bound_of_embedded_affine_chain_family
    {β : Type*} [Fintype β] {n s d : ℕ} (hd : Odd d)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g)
    (b : ZMod (2^s*d)) (x : β → ZMod (2^s*d)) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3))
    (hcover : n+2*(Fintype.card β)*Nat.log 2 n ≤ 2*(∑ i, L i)) : stratumBound n s ≤ 2^s*d := by
  classical
  have hn : 0 < n := by have := (e ⟨a,⟨0,by omega⟩⟩).isLt; omega
  obtain ⟨v,hv⟩ := exists_actual_affine_chain_family_of_embedding hn g b x L e hchain
  exact stratum_lower_bound_of_actual_affine_chain_family hd g hg b x L v hv a ha hcharge hcover

/-- Direct original G3 exclusion for arbitrary embedded families
meeting the combined-cover thresholds. -/
theorem not_validTuple_exceptional_of_embedded_affine_chain_family
    {β : Type*} [Fintype β] {n : ℕ} (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b : ZMod (2*globalBound (n-1))) (x : β → ZMod (2*globalBound (n-1))) (L : β → ℕ)
    (e : (Σ a, Fin (L a)) ↪ Fin n)
    (hchain : ∀ a (i : Fin (L a)), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (a : β) (ha : 4 ≤ L a)
    (hcharge : n^(Fintype.card β)*2^(n-∑ i, L i) ≤ 2^(L a-3))
    (hcover : n+2*(Fintype.card β)*Nat.log 2 n ≤ 2*(∑ i, L i)) : ¬ ValidTuple g := by
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
  have h := global_lower_bound_of_embedded_affine_chain_family g hg b x L e hchain a ha hcharge hcover
  omega

/-- For at least two equal-length chains, one logarithmic cutoff pays
both budgets. The one-third threshold is its r=2 instance. -/
theorem uniform_chain_family_cover_conditions
    {n r m : ℕ} (hr : 2 ≤ r) (hm : 4 ≤ m) (hsize : r*m ≤ n)
    (hcut : n+r*Nat.log 2 n+r+3 ≤ (r+1)*m) :
    n^r*2^(n-r*m) ≤ 2^(m-3) ∧ n+2*r*Nat.log 2 n ≤ 2*(r*m) := by
  have hn : 0 < n := by nlinarith
  have hsub := Nat.sub_add_cancel hsize
  refine ⟨partial_chain_forest_charge_of_logarithmic_cover (by omega) (by nlinarith),?_⟩
  have hlog := four_mul_log_two_le_add_four hn
  by_contra hnot
  have hb : 2*(r*m) < n+2*r*Nat.log 2 n := by omega
  have hb' := Nat.mul_lt_mul_of_pos_left hb (by omega : 0 < r+1)
  have hc' := Nat.mul_le_mul_left (2*r) hcut
  have hl' := Nat.mul_le_mul_left r hlog
  have hrn := Nat.mul_le_mul_right n hr
  nlinarith

/-- Uniform original global bound from ANY r disjoint equal affine
chains at the explicit n/(r+1) plus logarithmic cutoff, for r>=2. -/
theorem global_lower_bound_of_uniform_affine_chain_family
    {n r m N : ℕ} [NeZero N] (hr : 2 ≤ r) (hm : 4 ≤ m)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (b : ZMod N) (x : Fin r → ZMod N)
    (e : (Σ _a : Fin r, Fin m) ↪ Fin n)
    (hchain : ∀ a (i : Fin m), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (hcut : n+r*Nat.log 2 n+r+3 ≤ (r+1)*m) : globalBound n ≤ N := by
  have hsize : r*m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨hcharge,hcover⟩ := uniform_chain_family_cover_conditions hr hm hsize hcut
  exact global_lower_bound_of_embedded_affine_chain_family g hg b x (fun _ ↦ m) e hchain
    ⟨0,by omega⟩ hm (by simpa using hcharge) (by simpa using hcover)

/-- Every original exact-stratum bound at the same uniform cutoff. -/
theorem stratum_lower_bound_of_uniform_affine_chain_family
    {n r m s d : ℕ} (hd : Odd d) (hr : 2 ≤ r) (hm : 4 ≤ m)
    (g : Fin n → ZMod (2^s*d)) (hg : ValidTuple g) (b : ZMod (2^s*d)) (x : Fin r → ZMod (2^s*d))
    (e : (Σ _a : Fin r, Fin m) ↪ Fin n)
    (hchain : ∀ a (i : Fin m), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (hcut : n+r*Nat.log 2 n+r+3 ≤ (r+1)*m) : stratumBound n s ≤ 2^s*d := by
  have hsize : r*m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨hcharge,hcover⟩ := uniform_chain_family_cover_conditions hr hm hsize hcut
  exact stratum_lower_bound_of_embedded_affine_chain_family hd g hg b x (fun _ ↦ m) e hchain
    ⟨0,by omega⟩ hm (by simpa using hcharge) (by simpa using hcover)

/-- Direct original G3 exclusion for every uniform family at the same
cutoff, without any fixed bound on the number of chains. -/
theorem not_validTuple_exceptional_of_uniform_affine_chain_family
    {n r m : ℕ} (hr : 2 ≤ r) (hm : 4 ≤ m) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1)))
    (b : ZMod (2*globalBound (n-1))) (x : Fin r → ZMod (2*globalBound (n-1)))
    (e : (Σ _a : Fin r, Fin m) ↪ Fin n)
    (hchain : ∀ a (i : Fin m), g (e ⟨a,i⟩)+b=2^i.val • x a)
    (hcut : n+r*Nat.log 2 n+r+3 ≤ (r+1)*m) : ¬ ValidTuple g := by
  have hsize : r*m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨hcharge,hcover⟩ := uniform_chain_family_cover_conditions hr hm hsize hcut
  exact not_validTuple_exceptional_of_embedded_affine_chain_family hnpow g b x (fun _ ↦ m) e hchain
    ⟨0,by omega⟩ hm (by simpa using hcharge) (by simpa using hcover)

end MinModulus
