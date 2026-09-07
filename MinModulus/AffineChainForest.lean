import MinModulus.G1ThreeEscapeCycle

/-! Actual all-arity affine chain forests, extracted terminal geometry,
seed parity, and unconditional whole-tuple subbinary span. The original
critical three-escape G1 residual is reduced to three actual jointly
spanning chains with at least two odd seeds. Its arithmetic, and the
unrestricted G1/G2/G3 gates, remain open. -/

namespace MinModulus

/-- Every terminal basin is a complete ordered chain. This works for
an ARBITRARY terminal set, and the dependent sum covers every original
coordinate exactly once while retaining each actual terminal. -/
theorem exists_full_chain_forest_of_ranked_injective_map
    {α : Type*} [Fintype α] (R : α → α) (A : Finset α)
    (hfix : ∀ i, i ∈ A → R i=i) (r : α → ℕ)
    (hz : ∀ i, r i=0 ↔ i ∈ A) (hr : ∀ i, i ∉ A → r i=r (R i)+1)
    (hinj : ∀ i, i ∉ A → ∀ j, j ∉ A → R i=R j → i=j) :
    ∃ L : A → ℕ, (∀ a, 0 < L a) ∧ ∃ E : (Σ a : A, Fin (L a)) ≃ α,
      (∀ a (i : Fin (L a)), r (E ⟨a,i⟩)=L a-1-i.val) ∧
      (∀ a (i : Fin (L a)) (hi : i.val+1 < L a),
        R (E ⟨a,i⟩)=E ⟨a,⟨i.val+1,hi⟩⟩) ∧
      (∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val) := by
  classical
  have hterminal (i : α) : R^[r i] i ∈ A := by
    apply (hz _).mp
    simpa only [Nat.sub_self] using rank_iterate_before_terminal_set R (↑A : Set α) r hz hr i (le_refl _)
  let T : α → A := fun i ↦ ⟨R^[r i] i,hterminal i⟩
  have hTa (a : A) : T a.val=a := by
    apply Subtype.ext
    simp only [T,(hz a.val).mpr a.property,Function.iterate_zero,Function.id_def]
  have hTR (i : α) : T (R i)=T i := by
    by_cases hi : i ∈ A
    · rw [hfix i hi]
    · apply Subtype.ext
      change R^[r (R i)] (R i)=R^[r i] i
      rw [hr i hi,Function.iterate_succ_apply]
  let S := fun a : A ↦ {i : α // T i=a}
  have hchain : ∀ a : A, ∃ L, 0 < L ∧ ∃ e : Fin L ≃ S a,
      (∀ i, r (e i).val=L-1-i.val) ∧
      (∀ (i : Fin L) (hi : i.val+1 < L), R (e i).val=(e ⟨i.val+1,hi⟩).val) ∧
      (∀ i : Fin L, i.val+1=L → (e i).val=a.val) := by
    intro a
    let z : S a := ⟨a.val,hTa a⟩
    let Q : S a → S a := fun i ↦ ⟨R i.val,(hTR i.val).trans i.property⟩
    have hzero (i : S a) : r i.val=0 ↔ i=z := by
      constructor
      · intro hi
        have him := (hz i.val).mp hi
        have hh : (⟨i.val,him⟩ : A)=a := (hTa ⟨i.val,him⟩).symm.trans i.property
        have hv := congrArg (fun j : A ↦ j.val) hh
        exact Subtype.ext hv
      · intro hi
        subst i
        exact (hz a.val).mpr a.property
    have hnot (i : S a) (hi : i ≠ z) : i.val ∉ A := by
      intro him
      exact hi ((hzero i).mp ((hz i.val).mpr him))
    have hstep (i : S a) (hi : i ≠ z) : r i.val=r (Q i).val+1 := hr i.val (hnot i hi)
    have hqi : ∀ i : S a, i ≠ z → ∀ j : S a, j ≠ z → Q i=Q j → i=j := by
      intro i hi j hj he
      exact Subtype.ext (hinj i.val (hnot i hi) j.val (hnot j hj) (congrArg Subtype.val he))
    obtain ⟨L,hL,e,he,harrow,hend⟩ := exists_full_chain_of_ranked_injective_map Q z _ hzero hstep hqi
    refine ⟨L,hL,e,he,?_,?_⟩
    · intro i hi
      exact congrArg Subtype.val (harrow i hi)
    · intro i hi
      exact congrArg Subtype.val (hend i hi)
  choose L hL e he harrow hend using hchain
  let E : (Σ a : A, Fin (L a)) ≃ α := (Equiv.sigmaCongrRight e).trans (Equiv.sigmaFiberEquiv T)
  refine ⟨L,hL,E,?_,?_,?_⟩
  · intro a i
    exact he a i
  · intro a i hi
    exact harrow a i hi
  · intro a i hi
    exact hend a i hi

/-- Actual injective acyclic affine doubling outside ANY finite escape
set yields a full forest of actual dyadic chains. Every coordinate and
specified endpoint is retained, with no ValidTuple or normal-form input. -/
theorem exists_affine_chain_forest_of_injective_acyclic_doubling
    {α : Type*} [Fintype α] {G : Type*} [AddCommGroup G]
    (g : α → G) (hinj : Function.Injective (fun i ↦ 2 • g i))
    (A : Finset α) (b : G) (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hacyclic : ∀ {m : ℕ}, 0 < m → ∀ e : Fin m ↪ α, ∀ P : Equiv.Perm (Fin m),
      ¬ (∀ i, g (e (P i))=2 • g (e i)+b)) :
    ∃ L : A → ℕ, (∀ a, 0 < L a) ∧ (∑ a, L a)=Fintype.card α ∧
      ∃ E : (Σ a : A, Fin (L a)) ≃ α, ∃ x : A → G,
      (∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) ∧
      (∀ a (i : Fin (L a)), i.val+1=L a → E ⟨a,i⟩=a.val) := by
  classical
  let R : α → α := fun i ↦ if hi : i ∈ A then i else Classical.choose (hclosed i hi)
  have hfix : ∀ i, i ∈ A → R i=i := by intro i hi; simp only [R,dif_pos hi]
  have hd : ∀ i, i ∉ A → g (R i)=2 • g i+b := by
    intro i hi
    simpa only [R,dif_neg hi] using Classical.choose_spec (hclosed i hi)
  have hRi : ∀ i, i ∉ A → ∀ j, j ∉ A → R i=R j → i=j := by
    intro i hi j hj he
    apply hinj
    apply add_right_cancel (b := b)
    rw [← hd i hi,← hd j hj,he]
  rcases rank_or_nonempty_cycle_avoiding_set R (↑A : Set α) with ⟨r,hz,hr⟩ | ⟨m,hm,e,P,he,hP⟩
  · obtain ⟨L,hL,E,hEr,hEa,hEe⟩ := exists_full_chain_forest_of_ranked_injective_map R A hfix r hz hr hRi
    have hcard : (∑ a, L a)=Fintype.card α := by
      simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
    let x : A → G := fun a ↦ g (E ⟨a,⟨0,hL a⟩⟩)+b
    refine ⟨L,hL,hcard,E,x,?_,hEe⟩
    intro a
    apply powers_of_ordered_doubling_arrows (hL a)
    intro i hi
    have hnot : E ⟨a,i⟩ ∉ A := by
      intro h
      have h0 := (hz _).mpr h
      have hh := hEr a i
      omega
    rw [← hEa a i hi,hd _ hnot]
    simp only [two_nsmul]
    abel
  · exact (hacyclic hm e P (by intro i; rw [hP,hd _ (he i)])).elim

/-- With at most three proposed escapes, failed critical half descent
forces EXACTLY three genuine escapes. No redundant marked endpoints
remain in the forest extracted from the original data. -/
theorem exact_three_genuine_escapes_of_critical_without_half
    {n s q : ℕ} (hq : Odd q)
    (g : Fin (n+1) → ZMod (2^(s+1)*q)) (hg : ValidTuple g)
    (hc : 2^(s+1)*q < stratumBound (n+1) (s+1))
    (A : Finset (Fin (n+1))) (hA : A.card ≤ 3) (b : ZMod (2^(s+1)*q))
    (hclosed : ∀ i, i ∉ A → ∃ j, g j=2 • g i+b)
    (hnohalf : ¬ AdmitsValidTuple n (2^s*q)) :
    A.card=3 ∧ ∀ i, i ∈ A → ∀ j, g j ≠ 2 • g i+b := by
  classical
  let B := Finset.univ.filter (fun i ↦ ∀ j, g j ≠ 2 • g i+b)
  have hB : 3 ≤ B.card := three_le_affine_escape_card_of_critical_without_half hq g hg hc hnohalf b
  have hBA : B ⊆ A := by
    intro i hi
    by_contra hnot
    obtain ⟨j,hj⟩ := hclosed i hnot
    exact (Finset.mem_filter.mp hi).2 j hj
  have hcard := Finset.card_le_card hBA
  have hEq : B=A := Finset.eq_of_subset_of_card_le hBA (by omega)
  refine ⟨by omega,?_⟩
  intro i hi
  rw [← hEq] at hi
  exact (Finset.mem_filter.mp hi).2

/-- The ORIGINAL critical three-escape G1 residual supplies exactly
three full actual chains, indexed by their original genuine endpoints.
Lengths, seeds, rank geometry and coverage are all extracted, not assumed. -/
theorem exists_actual_three_chain_forest_of_critical_without_half
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
      (∀ a : A, ∀ j, g j ≠ 2 • g a.val+b) := by
  obtain ⟨hcard,hgenuine⟩ := exact_three_genuine_escapes_of_critical_without_half hq g hg hc A hA b hclosed hnohalf
  obtain ⟨hi,hacyclic⟩ := injective_and_acyclic_of_critical_three_escape_without_half hq hn
    g hg hc A hA b hclosed hnohalf
  obtain ⟨L,hL,hsize,E,x,hchain,hend⟩ :=
    exists_affine_chain_forest_of_injective_acyclic_doubling g hi A b hclosed hacyclic
  simp only [Fintype.card_fin] at hsize
  exact ⟨hcard,L,hL,hsize,E,x,hchain,hend,fun a ↦ hgenuine a.val a.property⟩

/-- In an arbitrary actual chain forest, failed half descent forces
at least TWO odd seeds. All nonseed coordinates are even after the
affine translation; no claim that every seed is odd is made. -/
theorem two_le_odd_seed_card_of_chain_forest_without_half
    {n N M : ℕ} [NeZero M] (hN : N=2*M) (hd : 2 ∣ N)
    {β : Type*} [Fintype β] (L : β → ℕ) (hL : ∀ a, 0 < L a)
    (g : Fin (n+1) → ZMod N) (hg : ValidTuple g)
    (E : (Σ a : β, Fin (L a)) ≃ Fin (n+1)) (x : β → ZMod N) (b : ZMod N)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a)
    (hnohalf : ¬ AdmitsValidTuple n M) :
    2 ≤ (Finset.univ.filter (fun a ↦ ZMod.castHom hd (ZMod 2) (x a)=1)).card := by
  classical
  let π := (ZMod.castHom hd (ZMod 2)).toAddMonoidHom
  let v : Fin (n+1) → ZMod N := fun i ↦ g i+b
  have hv : ValidTuple v := by
    simpa only [v,sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  obtain hhalf | ⟨_,hodd⟩ := admitsValidTuple_half_or_two_large_parity_fibres_of_eq_two_mul hN hd v hv
  · exact (hnohalf hhalf).elim
  let F := Finset.univ.filter (fun i ↦ π (v i)=1)
  let S := Finset.univ.filter (fun a ↦ π (x a)=1)
  let f : Fin (n+1) → β := fun i ↦ (E.symm i).1
  let seed : β → Fin (n+1) := fun a ↦ E ⟨a,⟨0,hL a⟩⟩
  have hi0 : ∀ i, i ∈ F → (E.symm i).2.val=0 := by
    intro i hi
    by_contra hnot
    have hz := parity_two_pow_smul_eq_zero_of_pos π (x (f i)) (by omega : 0 < (E.symm i).2.val)
    have hh := congrArg π (hchain (E.symm i).1 (E.symm i).2)
    have hp : π (v i)=1 := (Finset.mem_filter.mp hi).2
    have hz' : π (v i)=0 := by
      calc
        _=π (2^(E.symm i).2.val • x (f i)) := by simpa only [v,f,E.apply_symm_apply] using hh
        _=0 := hz
    have he : (0 : ZMod 2)=1 := hz'.symm.trans hp
    exact zero_ne_one he
  have hseed : ∀ i, i ∈ F → seed (f i)=i := by
    intro i hi
    have hs : (⟨f i,⟨0,hL (f i)⟩⟩ : Σ a : β, Fin (L a))=E.symm i := by
      have hh : (⟨0,hL (f i)⟩ : Fin (L (f i)))=(E.symm i).2 := Fin.ext (hi0 i hi).symm
      exact congrArg (Sigma.mk (f i)) hh
    exact (congrArg E hs).trans (E.apply_symm_apply i)
  have hfi : Set.InjOn f (↑F : Set (Fin (n+1))) := by
    intro i hi j hj he
    exact (hseed i hi).symm.trans ((congrArg seed he).trans (hseed j hj))
  have hsub : F.image f ⊆ S := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    have hh : g i+b=x (f i) := by
      simpa only [E.apply_symm_apply,hi0 i hi,pow_zero,one_nsmul,f] using
        hchain (E.symm i).1 (E.symm i).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rw [← hh]
    exact (Finset.mem_filter.mp hi).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hfi] at hc
  change 2 ≤ S.card
  have ho : 2 ≤ F.card := hodd
  omega

/-- The original acyclic three-escape residual retains at least TWO
odd seeds, not an unjustified all-odd or individual-unit normalization. -/
theorem exists_two_odd_seed_three_chain_forest_of_critical_without_half
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
      2 ≤ (Finset.univ.filter (fun a ↦ Odd (x a).val)).card := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  letI : NeZero (2^s*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  have hN : 2^(s+1)*q=2*(2^s*q) := by rw [pow_succ',mul_assoc]
  have hd : 2 ∣ 2^(s+1)*q := by rw [hN]; exact dvd_mul_right 2 _
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine⟩ :=
    exists_actual_three_chain_forest_of_critical_without_half hq hn g hg hc A hA b hclosed hnohalf
  have hp := two_le_odd_seed_card_of_chain_forest_without_half hN hd L hL g hg E x b hchain hnohalf
  have hsub : (Finset.univ.filter (fun a ↦ ZMod.castHom hd (ZMod 2) (x a)=1)) ⊆
      Finset.univ.filter (fun a ↦ Odd (x a).val) := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,odd_val_of_parity_eq_one hd (x a) (Finset.mem_filter.mp ha).2⟩
  exact ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hp.trans (Finset.card_le_card hsub)⟩

/-- Every positive-length valid subbinary tuple generates the whole
ambient finite group, even after an arbitrary translation. This is a
general cube-index obstruction, with NO chain or parity assumption. -/
theorem subgroup_eq_top_of_valid_subbinary_translate
    {n : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (n+1) → G) (hg : ValidTuple g)
    (hcard : Fintype.card G < 2^(n+1)) (b : G)
    (S : AddSubgroup G) (hmem : ∀ i, g i+b ∈ S) : S=⊤ := by
  classical
  letI : Fintype S := Fintype.ofFinite S
  let v : Fin (n+1) → G := fun i ↦ g i+b
  have hv : ValidTuple v := by
    simpa only [v,sub_neg_eq_add] using validTuple_sub_const g hg (-b)
  let w : Fin (n+1) → S := fun i ↦ ⟨v i,hmem i⟩
  have hw : ValidTuple w := validTuple_of_comp S.subtype hv
  have hp := card_ge w hw
  have hi := S.card_mul_index
  simp only [Nat.card_eq_fintype_card] at hi
  have hG : 0 < Fintype.card G := Fintype.card_pos
  by_contra hproper
  have hi0 : S.index ≠ 0 := by intro hz; rw [hz,mul_zero] at hi; omega
  have hi1 : S.index ≠ 1 := by intro ho; exact hproper (AddSubgroup.index_eq_one.mp ho)
  have hi2 : 2 ≤ S.index := by omega
  have hh := Nat.mul_le_mul_left (Fintype.card S) hi2
  rw [pow_succ'] at hcard
  nlinarith only [hp,hi,hh,hcard]

/-- Every translate of the entire subbinary valid tuple spans the
group. This does NOT assert full span after each deletion. -/
theorem affine_span_eq_top_of_valid_subbinary
    {n : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    (g : Fin (n+1) → G) (hg : ValidTuple g)
    (hcard : Fintype.card G < 2^(n+1)) (b : G) :
    AddSubgroup.closure (Set.range (fun i ↦ g i+b))=⊤ := by
  apply subgroup_eq_top_of_valid_subbinary_translate g hg hcard b
  intro i
  exact AddSubgroup.subset_closure ⟨i,rfl⟩

/-- An arbitrary full actual chain forest jointly generates the group
in the subbinary regime. Individual seeds need not be units. -/
theorem seed_span_eq_top_of_valid_subbinary_chain_forest
    {n : ℕ} {G : Type*} [AddCommGroup G] [Fintype G]
    {β : Type*} [Fintype β] (L : β → ℕ)
    (g : Fin (n+1) → G) (hg : ValidTuple g)
    (hcard : Fintype.card G < 2^(n+1))
    (E : (Σ a : β, Fin (L a)) ≃ Fin (n+1)) (x : β → G) (b : G)
    (hchain : ∀ a (i : Fin (L a)), g (E ⟨a,i⟩)+b=2^i.val • x a) :
    AddSubgroup.closure (Set.range x)=⊤ := by
  apply subgroup_eq_top_of_valid_subbinary_translate g hg hcard b
  intro i
  have hh := hchain (E.symm i).1 (E.symm i).2
  simp only [E.apply_symm_apply] at hh
  rw [hh]
  exact (AddSubgroup.closure (Set.range x)).nsmul_mem
    (AddSubgroup.subset_closure ⟨(E.symm i).1,rfl⟩) _

/-- The original critical three-escape residual yields an actual
three-chain forest with joint FULL span and at least two odd seeds.
No unit, supplied normal form or deleted-span premise is used. -/
theorem exists_spanning_three_chain_forest_of_critical_without_half
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
      AddSubgroup.closure (Set.range x)=⊤ := by
  classical
  letI : NeZero (2^(s+1)*q) := ⟨(mul_pos (by positivity) hq.pos).ne'⟩
  obtain ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd⟩ :=
    exists_two_odd_seed_three_chain_forest_of_critical_without_half hq hn g hg hc A hA b hclosed hnohalf
  have hN : Fintype.card (ZMod (2^(s+1)*q)) < 2^(n+1) := by
    rw [ZMod.card]
    exact lt_of_lt_of_le hc (by unfold stratumBound; exact Nat.sub_le _ _)
  exact ⟨hcard,L,hL,hsize,E,x,hchain,hend,hgenuine,hodd,
    seed_span_eq_top_of_valid_subbinary_chain_forest L g hg hN E x b hchain⟩

end MinModulus
