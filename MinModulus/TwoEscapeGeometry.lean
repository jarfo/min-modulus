import MinModulus.G1TwoEscapeCycle

/-! Extract actual two-chain geometry from injective acyclic two-escape
data. Finite first-hit ranks and the two terminal basins supply the
decomposition; no proposed chain normal form is an input. -/

namespace MinModulus
open Finset Function

/-- First-hit rank for an arbitrary set of allowed terminal coordinates. -/
theorem exists_rank_of_all_orbits_hit_set
    {α : Type*} (R : α → α) (A : Set α)
    (hhit : ∀ i, ∃ t : ℕ, R^[t] i ∈ A) :
    ∃ r : α → ℕ, (∀ i, r i=0 ↔ i ∈ A) ∧
      ∀ i, i ∉ A → r i=r (R i)+1 := by
  classical
  let r : α → ℕ := fun i ↦ Nat.find (hhit i)
  have hr (i : α) : R^[r i] i ∈ A := Nat.find_spec (hhit i)
  have hmin (i : α) (t : ℕ) (ht : R^[t] i ∈ A) : r i ≤ t := Nat.find_min' (hhit i) ht
  have hz (i : α) : r i=0 ↔ i ∈ A := by simp [r]
  refine ⟨r,hz,?_⟩
  intro i hi
  have hp : 0 < r i := Nat.pos_of_ne_zero (fun h ↦ hi ((hz i).mp h))
  have hpred : r (R i) ≤ r i-1 := by
    apply hmin
    rw [← iterate_succ_apply,show (r i-1).succ=r i by omega]
    exact hr i
  have hsucc : r i ≤ r (R i)+1 := by
    apply hmin
    rw [iterate_succ_apply]
    exact hr (R i)
  omega

/-- A finite map either reaches the proposed terminal set everywhere,
or contains an actual nonempty periodic block avoiding that entire set. -/
theorem rank_or_nonempty_cycle_avoiding_set
    {α : Type*} [Fintype α] (R : α → α) (A : Set α) :
    (∃ r : α → ℕ, (∀ i, r i=0 ↔ i ∈ A) ∧ ∀ i, i ∉ A → r i=r (R i)+1) ∨
      ∃ m, 0 < m ∧ ∃ e : Fin m ↪ α, ∃ P : Equiv.Perm (Fin m),
        (∀ i, e i ∉ A) ∧ ∀ i, e (P i)=R (e i) := by
  classical
  by_cases hhit : ∀ i, ∃ t : ℕ, R^[t] i ∈ A
  · exact Or.inl (exists_rank_of_all_orbits_hit_set R A hhit)
  · right
    obtain ⟨i,hi⟩ : ∃ i, ∀ t : ℕ, R^[t] i ∉ A := by simpa using hhit
    let D : Set α := {j | ∀ t : ℕ, R^[t] j ∉ A}
    let T : D → D := fun j ↦ ⟨R j.val,fun t ht ↦ j.property (t+1) (by
      rw [iterate_succ_apply]; exact ht)⟩
    obtain ⟨k,hk⟩ := exists_periodic_iterate_finite T (⟨i,hi⟩ : D)
    let C := periodicPts T
    let m := Fintype.card C
    have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨⟨_,hk⟩⟩
    let δ : Fin m ≃ C := (Fintype.equivFin C).symm
    let p : Equiv.Perm C := (bijOn_periodicPts T).equiv T
    let P : Equiv.Perm (Fin m) := δ.trans (p.trans δ.symm)
    let e : Fin m ↪ α := δ.toEmbedding.trans
      ((Function.Embedding.subtype C).trans (Function.Embedding.subtype D))
    refine ⟨m,hm,e,P,?_,?_⟩
    · intro j
      exact (δ j).val.property 0
    · intro j
      simp [e,P,p,Set.BijOn.equiv]
      rfl

/-- A rank decreases exactly until its first hit on a terminal set. -/
theorem rank_iterate_before_terminal_set
    {α : Type*} (R : α → α) (A : Set α) (r : α → ℕ)
    (hz : ∀ i, r i=0 ↔ i ∈ A) (hr : ∀ i, i ∉ A → r i=r (R i)+1)
    (i : α) {t : ℕ} (ht : t ≤ r i) : r (R^[t] i)=r i-t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he := ih (by omega)
    have hne : R^[t] i ∉ A := by
      intro h
      have := (hz _).mpr h
      omega
    have hd := hr _ hne
    rw [iterate_succ_apply']
    omega

/-- Two terminal basins are complete disjoint chains whenever rank
decreases and the actual nonterminal arrows are injective. -/
theorem exists_two_full_chains_of_ranked_injective_map
    {α : Type*} [Fintype α] (R : α → α) (a b : α) (hab : a ≠ b)
    (ha : R a=a) (hb : R b=b) (r : α → ℕ)
    (hz : ∀ i, r i=0 ↔ i=a ∨ i=b)
    (hr : ∀ i, i ≠ a → i ≠ b → r i=r (R i)+1)
    (hinj : ∀ i, i ≠ a → i ≠ b → ∀ j, j ≠ a → j ≠ b → R i=R j → i=j) :
    ∃ A L, 0 < A ∧ 0 < L ∧ ∃ E : Fin (A+L) ≃ α,
      (∀ i : Fin A, r (E (Fin.castAdd L i))=A-1-i.val) ∧
      (∀ i : Fin L, r (E (Fin.natAdd A i))=L-1-i.val) ∧
      (∀ i : Fin A, ∀ hi : i.val+1 < A,
        R (E (Fin.castAdd L i))=E (Fin.castAdd L ⟨i.val+1,hi⟩)) ∧
      (∀ i : Fin L, ∀ hi : i.val+1 < L,
        R (E (Fin.natAdd A i))=E (Fin.natAdd A ⟨i.val+1,hi⟩)) ∧
      (∀ i : Fin A, i.val+1=A → E (Fin.castAdd L i)=a) ∧
      (∀ i : Fin L, i.val+1=L → E (Fin.natAdd A i)=b) := by
  classical
  let T : α → α := fun i ↦ R^[r i] i
  have hT (i : α) : T i=a ∨ T i=b := by
    apply (hz _).mp
    have hh := rank_iterate_before_terminal_set R {j | j=a ∨ j=b} r hz
      (fun j hj ↦ hr j (fun h ↦ hj (Or.inl h)) (fun h ↦ hj (Or.inr h))) i (le_refl _)
    simpa only [T,Nat.sub_self] using hh
  have hTa : T a=a := by simp [T,(hz a).mpr (Or.inl rfl)]
  have hTb : T b=b := by simp [T,(hz b).mpr (Or.inr rfl)]
  have hTR (i : α) : T (R i)=T i := by
    by_cases hia : i=a
    · simp only [hia,ha]
    by_cases hib : i=b
    · simp only [hib,hb]
    change R^[r (R i)] (R i)=R^[r i] i
    rw [hr i hia hib,iterate_succ_apply]
  let S : Set α := {i | T i=a}
  let U : Set α := Sᶜ
  have haS : a ∈ S := hTa
  have hbU : b ∈ U := by
    change T b ≠ a
    rw [hTb]
    exact Ne.symm hab
  let a' : S := ⟨a,haS⟩
  let b' : U := ⟨b,hbU⟩
  let Q : S → S := fun i ↦ ⟨R i.val,(hTR i.val).trans i.property⟩
  let V : U → U := fun i ↦ ⟨R i.val,fun he ↦ i.property ((hTR i.val).symm.trans he)⟩
  have hSb (i : S) : i.val ≠ b := by
    intro he
    exact hbU (he ▸ i.property)
  have hUa (i : U) : i.val ≠ a := fun he ↦ i.property (he ▸ haS)
  have hSz (i : S) : r i.val=0 ↔ i=a' := by
    constructor
    · intro h
      exact Subtype.ext ((hz i.val).mp h |>.resolve_right (hSb i))
    · intro h
      exact (hz i.val).mpr (Or.inl (congrArg Subtype.val h))
  have hUz (i : U) : r i.val=0 ↔ i=b' := by
    constructor
    · intro h
      exact Subtype.ext ((hz i.val).mp h |>.resolve_left (hUa i))
    · intro h
      exact (hz i.val).mpr (Or.inr (congrArg Subtype.val h))
  have hSr (i : S) (hi : i ≠ a') : r i.val=r (Q i).val+1 :=
    hr i.val (fun he ↦ hi (Subtype.ext he)) (hSb i)
  have hUr (i : U) (hi : i ≠ b') : r i.val=r (V i).val+1 :=
    hr i.val (hUa i) (fun he ↦ hi (Subtype.ext he))
  have hSi : ∀ i : S, i ≠ a' → ∀ j : S, j ≠ a' → Q i=Q j → i=j := by
    intro i hi j hj he
    exact Subtype.ext (hinj i.val (fun h ↦ hi (Subtype.ext h)) (hSb i)
      j.val (fun h ↦ hj (Subtype.ext h)) (hSb j) (congrArg Subtype.val he))
  have hUi : ∀ i : U, i ≠ b' → ∀ j : U, j ≠ b' → V i=V j → i=j := by
    intro i hi j hj he
    exact Subtype.ext (hinj i.val (hUa i) (fun h ↦ hi (Subtype.ext h))
      j.val (hUa j) (fun h ↦ hj (Subtype.ext h)) (congrArg Subtype.val he))
  obtain ⟨A,hA,γ,hγr,hγ,hlasta⟩ := exists_full_chain_of_ranked_injective_map Q a' _ hSz hSr hSi
  obtain ⟨L,hL,δ,hδr,hδ,hlastb⟩ := exists_full_chain_of_ranked_injective_map V b' _ hUz hUr hUi
  let join : S ⊕ U → α := Sum.elim Subtype.val Subtype.val
  have hjoin : Function.Bijective join := by
    constructor
    · rintro (i | i) (j | j) he
      · exact congrArg Sum.inl (Subtype.ext he)
      · change i.val=j.val at he
        exact False.elim (j.property (he ▸ i.property))
      · change i.val=j.val at he
        exact False.elim (i.property (he ▸ j.property))
      · exact congrArg Sum.inr (Subtype.ext he)
    · intro i
      by_cases hi : i ∈ S
      · exact ⟨Sum.inl ⟨i,hi⟩,rfl⟩
      · exact ⟨Sum.inr ⟨i,hi⟩,rfl⟩
  let E : Fin (A+L) ≃ α := finSumFinEquiv.symm.trans
    ((Equiv.sumCongr γ δ).trans (Equiv.ofBijective join hjoin))
  have hleft (i : Fin A) : E (Fin.castAdd L i)=(γ i).val := by simp [E,join]
  have hright (i : Fin L) : E (Fin.natAdd A i)=(δ i).val := by simp [E,join]
  refine ⟨A,L,hA,hL,E,?_,?_,?_,?_,?_,?_⟩
  · intro i
    rw [hleft]
    exact hγr i
  · intro i
    rw [hright]
    exact hδr i
  · intro i hi
    simp only [hleft]
    exact congrArg Subtype.val (hγ i hi)
  · intro i hi
    simp only [hright]
    exact congrArg Subtype.val (hδ i hi)
  · intro i hi
    rw [hleft]
    exact congrArg Subtype.val (hlasta i hi)
  · intro i hi
    rw [hright]
    exact congrArg Subtype.val (hlastb i hi)

/-- Actual injective affine doubling with two proposed escapes and no
actual cycle consists of exactly two full disjoint chains. The original
terminal coordinates, affine offset and seed values are retained. -/
theorem exists_two_affine_chains_of_injective_acyclic_two_escapes
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hinj : Function.Injective (fun i ↦ 2 • g i))
    (a z : Fin n) (haz : a ≠ z) (b : G)
    (hclosed : ∀ i, i ≠ a → i ≠ z → ∃ j, g j=2 • g i+b)
    (hacyclic : ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ Fin n, ∀ P : Equiv.Perm (Fin m),
      ¬ (∀ i, g (e (P i))=2 • g (e i)+b)) :
    ∃ A L, 0 < A ∧ 0 < L ∧ A+L=n ∧ ∃ E : Fin (A+L) ≃ Fin n, ∃ x y : G,
      (∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x) ∧
      (∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y) ∧
      (∀ i : Fin A, i.val+1=A → E (Fin.castAdd L i)=a) ∧
      (∀ i : Fin L, i.val+1=L → E (Fin.natAdd A i)=z) := by
  classical
  let R : Fin n → Fin n := fun i ↦ if hi : i=a ∨ i=z then i
    else Classical.choose (hclosed i (fun h ↦ hi (Or.inl h)) (fun h ↦ hi (Or.inr h)))
  have hd (i : Fin n) (hi : ¬ (i=a ∨ i=z)) : g (R i)=2 • g i+b := by
    simpa only [R,dif_neg hi] using
      Classical.choose_spec (hclosed i (fun h ↦ hi (Or.inl h)) (fun h ↦ hi (Or.inr h)))
  have hRi : ∀ i, i ≠ a → i ≠ z → ∀ j, j ≠ a → j ≠ z → R i=R j → i=j := by
    intro i hia hiz j hja hjz he
    apply hinj
    apply add_right_cancel (b := b)
    rw [← hd i (by tauto),← hd j (by tauto),he]
  rcases rank_or_nonempty_cycle_avoiding_set R {i | i=a ∨ i=z} with
    ⟨r,hzero,hrank⟩ | ⟨m,hm,e,P,he,hP⟩
  · have hz : ∀ i, r i=0 ↔ i=a ∨ i=z := hzero
    obtain ⟨A,L,hA,hL,E,hrA,hrL,hnextA,hnextL,hlastA,hlastL⟩ :=
      exists_two_full_chains_of_ranked_injective_map R a z haz
        (by simp [R]) (by simp [R]) r hz (fun i hi hj ↦ hrank i (by simp [hi,hj])) hRi
    have hn : A+L=n := by simpa using Fintype.card_congr E
    have hleft : ∀ i : Fin A, g (E (Fin.castAdd L i))+b=
        2^i.val • (g (E (Fin.castAdd L ⟨0,hA⟩))+b) := by
      apply powers_of_ordered_doubling_arrows hA
      intro i hi
      have hne : ¬ (E (Fin.castAdd L i)=a ∨ E (Fin.castAdd L i)=z) := by
        intro h
        have h0 := (hz _).mpr h
        have hh := hrA i
        omega
      rw [← hnextA i hi,hd _ hne,smul_add]
      abel
    have hright : ∀ i : Fin L, g (E (Fin.natAdd A i))+b=
        2^i.val • (g (E (Fin.natAdd A ⟨0,hL⟩))+b) := by
      apply powers_of_ordered_doubling_arrows hL
      intro i hi
      have hne : ¬ (E (Fin.natAdd A i)=a ∨ E (Fin.natAdd A i)=z) := by
        intro h
        have h0 := (hz _).mpr h
        have hh := hrL i
        omega
      rw [← hnextL i hi,hd _ hne,smul_add]
      abel
    exact ⟨A,L,hA,hL,hn,E,_,_,hleft,hright,hlastA,hlastL⟩
  · exact False.elim (hacyclic hm e P (fun i ↦ by rw [hP,hd _ (he i)]))

/-- Criticality makes the two allowed escapes actual and distinct.
Failure of G1 half descent then extracts the full two-chain normal form;
no injectivity, acyclicity, rank or decomposition remains as an input. -/
theorem exists_two_affine_chains_of_critical_two_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 3 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (B : Finset (Fin (n+1))) (hB : B.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    ∃ A L, 0 < A ∧ 0 < L ∧ A+L=n+1 ∧ ∃ E : Fin (A+L) ≃ Fin (n+1),
      ∃ x y : ZMod (2^(s+1)*q),
      (∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x) ∧
      (∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y) ∧
      (∀ i : Fin A, i.val+1=A → ∀ j, g j ≠ 2 • g (E (Fin.castAdd L i))+b) ∧
      (∀ i : Fin L, i.val+1=L → ∀ j, g j ≠ 2 • g (E (Fin.natAdd A i))+b) := by
  classical
  obtain ⟨hi,hacyclic⟩ := injective_and_acyclic_of_critical_two_escape_without_half
    hq hn g hg hcritical B hB b hclosed hnohalf
  obtain ⟨a,z,haz,ha,hz⟩ := two_affine_doubling_escapes_of_valid_below_stratumBound
    (by omega) hq g hg hcritical b
  have haB : a ∈ B := by
    by_contra h
    obtain ⟨j,hj⟩ := hclosed a h
    exact ha j hj
  have hzB : z ∈ B := by
    by_contra h
    obtain ⟨j,hj⟩ := hclosed z h
    exact hz j hj
  have hpair : ({a,z} : Finset (Fin (n+1))) ⊆ B := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact haB
    · exact Finset.mem_singleton.mp hi ▸ hzB
  have hBeq : B={a,z} := (Finset.eq_of_subset_of_card_le hpair (by simpa [haz] using hB)).symm
  obtain ⟨A,L,hA,hL,hsize,E,x,y,hleft,hright,hlasta,hlastz⟩ :=
    exists_two_affine_chains_of_injective_acyclic_two_escapes g hi a z haz b
      (fun i hia hiz ↦ hclosed i (by simp [hBeq,hia,hiz])) hacyclic
  refine ⟨A,L,hA,hL,hsize,E,x,y,hleft,hright,?_,?_⟩
  · intro i hi j
    rw [hlasta i hi]
    exact ha j
  · intro i hi j
    rw [hlastz i hi]
    exact hz j

/-- The completed packing theorem now bounds the ORIGINAL critical
two-escape G1 residual, without a supplied two-chain decomposition. -/
theorem near_binary_bound_of_critical_two_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 4 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (B : Finset (Fin (n+1))) (hB : B.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    4*2^(n+1) ≤ 4*(2^(s+1)*q)+(n+2)^2 := by
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨A,L,hA,hL,hsize,E,x,y,hleft,hright,_,_⟩ :=
    exists_two_affine_chains_of_critical_two_escape_without_half hq (by omega)
      g hg hcritical B hB b hclosed hnohalf
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hh := near_binary_card_bound_of_valid_two_chains hA hL (by omega) _ hv x y hleft hright
  simpa only [ZMod.card,hsize,Nat.add_assoc] using hh

/-- A remaining critical two-escape G1 tuple supplies an ACTUAL small
dyadic-sided corner paying for its entire binary deficit. Both original
chains and their affine seed relation are extracted, not supplied. -/
theorem exists_deficit_corner_of_critical_two_escape_without_half
    {n s q : ℕ} (hq : Odd q) (hn : 4 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (B : Finset (Fin (n+1))) (hB : B.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    ∃ A L, 0 < A ∧ 0 < L ∧ A+L=n+1 ∧ ∃ E : Fin (A+L) ≃ Fin (n+1),
      ∃ x y : ZMod (2^(s+1)*q),
      (∀ i : Fin A, g (E (Fin.castAdd L i))+b=2^i.val • x) ∧
      (∀ i : Fin L, g (E (Fin.natAdd A i))+b=2^i.val • y) ∧
      ∃ d u : ℕ, 0 < d ∧ d ≤ 2^A ∧ 0 < u ∧ u ≤ 2^L ∧
        d+u ≤ n+2 ∧ 2^(n+1) ≤ 2^(s+1)*q+d*u ∧
        ((∃ e, d=2^e) ∨ ∃ f, u=2^f) ∧
        (2^A-d) • x+(2^L-u) • y=0 := by
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨A,L,hA,hL,hsize,E,x,y,hleft,hright,_,_⟩ :=
    exists_two_affine_chains_of_critical_two_escape_without_half hq (by omega)
      g hg hcritical B hB b hclosed hnohalf
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hpow : 2^(s+1)*q < 2^(n+1) := lt_of_lt_of_le hcritical (Nat.sub_le _ _)
  have hc : Fintype.card (ZMod (2^(s+1)*q)) < 2^(A+L) := by simpa [hsize] using hpow
  have hh := exists_deficit_corner_of_valid_subbinary_two_chains hA hL (by omega)
    _ hv x y hleft hright hc
  refine ⟨A,L,hA,hL,hsize,E,x,y,hleft,hright,?_⟩
  simpa only [ZMod.card,hsize,Nat.add_assoc] using hh

/-- Uniform actual G1 descent holds throughout the large-deficit
two-escape region. Only the quadratic-width band can remain in this
class; this is not asserted to close the sharp global threshold. -/
theorem admitsValidTuple_half_of_critical_two_escape_large_deficit
    {n s q : ℕ} (hq : Odd q) (hn : 4 ≤ n)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hcritical : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (B : Finset (Fin (n+1))) (hB : B.card ≤ 2) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ B → ∃ j, g j=2 • g i+b)
    (hgap : 4*(2^(s+1)*q)+(n+2)^2 < 4*2^(n+1)) : AdmitsValidTuple n (2^s*q) := by
  by_contra hnohalf
  have hh := near_binary_bound_of_critical_two_escape_without_half
    hq hn g hg hcritical B hB b hclosed hnohalf
  omega

end MinModulus
