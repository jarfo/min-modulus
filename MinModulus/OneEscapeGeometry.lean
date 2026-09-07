import MinModulus.ShallowForkWeights

/-!
# Extract all one-escape geometry and close its exceptional lift

In a finite rooted graph with only one collision pair, a longest chain
has an injective complement with a unique exit. First-hit ranks extract
that complement as a second chain, with the required arm ordering.
If some orbit never hits the escape, its periodic block gives an actual
cycle. Validity and cyclic two-torsion supply the collision restriction.

Thus ALL one-escape affine-doubling tuples are excluded at the G3 modulus:
no rank, acyclicity, permutation, chain, fork, seed, order, or depth input
remains. The dimension-three base uses the general equality-order theorem,
not a tuple census. Arbitrary tuples are not known to have one-escape
closure; the three unrestricted global gates remain open.
-/

namespace MinModulus
open Finset Function

/-- First-hit distance supplies a strictly decreasing rank away from an
absorbing endpoint. This construction has no arithmetic assumptions. -/
theorem exists_rank_of_all_orbits_hit
    {α : Type*} (R : α → α) (a : α)
    (hhit : ∀ i, ∃ t : ℕ, R^[t] i=a) :
    ∃ r : α → ℕ, (∀ i, r i=0 ↔ i=a) ∧
      ∀ i, i ≠ a → r i=r (R i)+1 := by
  classical
  let r : α → ℕ := fun i ↦ Nat.find (hhit i)
  have hr (i : α) : R^[r i] i=a := Nat.find_spec (hhit i)
  have hmin (i : α) (t : ℕ) (ht : R^[t] i=a) : r i ≤ t := Nat.find_min' (hhit i) ht
  have hz (i : α) : r i=0 ↔ i=a := by simp [r]
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

/-- A decreasing rank measures every initial segment before its endpoint. -/
theorem rank_iterate_before_root
    {α : Type*} (R : α → α) (a : α) (r : α → ℕ)
    (hz : ∀ i, r i=0 ↔ i=a) (hr : ∀ i, i ≠ a → r i=r (R i)+1)
    (i : α) {t : ℕ} (ht : t ≤ r i) : r (R^[t] i)=r i-t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have he := ih (by omega)
    have hne : R^[t] i ≠ a := by
      intro h
      have := (hz _).mpr h
      omega
    have hd := hr _ hne
    rw [iterate_succ_apply']
    omega

/-- If predecessor collisions are absent, rank itself is injective. -/
theorem rank_injective_of_injective_off_root
    {α : Type*} (R : α → α) (a : α) (r : α → ℕ)
    (hz : ∀ i, r i=0 ↔ i=a) (hr : ∀ i, i ≠ a → r i=r (R i)+1)
    (hinj : ∀ i, i ≠ a → ∀ j, j ≠ a → R i=R j → i=j) :
    Function.Injective r := by
  intro i j heq
  have aux : ∀ t, ∀ i j, r i=t → r j=t → i=j := by
    intro t
    induction t with
    | zero => intro i j hi hj; exact ((hz i).mp hi).trans ((hz j).mp hj).symm
    | succ t ih =>
      intro i j hi hj
      have hia : i ≠ a := fun h ↦ by have := (hz i).mpr h; omega
      have hja : j ≠ a := fun h ↦ by have := (hz j).mpr h; omega
      have hri := hr i hia
      have hrj := hr j hja
      exact hinj i hia j hja (ih (R i) (R j) (by omega) (by omega))
  exact aux (r i) i j rfl heq.symm

/-- A finite acyclic map injective away from its endpoint is one full
ordered chain. The original endpoint and each actual arrow are retained. -/
theorem exists_full_chain_of_ranked_injective_map
    {α : Type*} [Fintype α] (R : α → α) (a : α) (r : α → ℕ)
    (hz : ∀ i, r i=0 ↔ i=a) (hr : ∀ i, i ≠ a → r i=r (R i)+1)
    (hinj : ∀ i, i ≠ a → ∀ j, j ≠ a → R i=R j → i=j) :
    ∃ L, 0 < L ∧ ∃ E : Fin L ≃ α,
      (∀ i, r (E i)=L-1-i.val) ∧
      (∀ i : Fin L, ∀ hi : i.val+1 < L,
        R (E i)=E ⟨i.val+1,hi⟩) ∧ (∀ i : Fin L, i.val+1=L → E i=a) := by
  classical
  obtain ⟨s,_,hs⟩ := Finset.exists_max_image Finset.univ r ⟨a,Finset.mem_univ _⟩
  have hri := rank_injective_of_injective_off_root R a r hz hr hinj
  let f : Fin (r s+1) → α := fun i ↦ R^[i.val] s
  have hf (i : Fin (r s+1)) : r (f i)=r s-i.val :=
    rank_iterate_before_root R a r hz hr s (by omega)
  have hfi : Function.Injective f := by
    intro i j heq
    have he := congrArg r heq
    rw [hf,hf] at he
    apply Fin.ext
    omega
  have hfs : Function.Surjective f := by
    intro i
    have hi := hs i (Finset.mem_univ _)
    refine ⟨⟨r s-r i,by omega⟩,hri ?_⟩
    rw [hf]
    change r s-(r s-r i)=r i
    omega
  let E := Equiv.ofBijective f ⟨hfi,hfs⟩
  refine ⟨r s+1,by omega,E,?_,?_,?_⟩
  · intro i
    exact (hf i).trans (by omega)
  · intro i hi
    change R (R^[i.val] s)=R^[i.val+1] s
    rw [iterate_succ_apply']
  · intro i hi
    apply (hz _).mp
    change r (f _)=0
    rw [hf]
    omega

/-- Remove a longest rootward chain. If anything remains, there is a
unique boundary predecessor, and the complement is itself an injective
one-endpoint map. The only combinatorial input is one collision pair. -/
theorem exists_chain_and_injective_complement_of_ranked_one_collision
    {α : Type*} [Fintype α] (R : α → α) (a : α) (r : α → ℕ)
    (hz : ∀ i, r i=0 ↔ i=a) (hr : ∀ i, i ≠ a → r i=r (R i)+1)
    (hpair : ∀ u v, u ≠ a → v ≠ a → u ≠ v → R u=R v →
      ∀ i j, i ≠ a → j ≠ a → i ≠ j → R i=R j → i=u ∨ i=v) :
    ∃ L, 0 < L ∧ ∃ f : Fin L ↪ α,
      (∀ i, r (f i)=L-1-i.val) ∧ (∀ i, r i < L) ∧
      (∀ i : Fin L, ∀ hi : i.val+1 < L, R (f i)=f ⟨i.val+1,hi⟩) ∧
      (∀ i : Fin L, i.val+1=L → f i=a) ∧
      (Function.Surjective f ∨
        ∃ c, c ∉ Set.range f ∧ ∃ B : Fin L, 0 < B.val ∧ R c=f B ∧
          (∀ i, i ∉ Set.range f → i ≠ c → R i ∉ Set.range f) ∧
          Set.InjOn R (Set.range f)ᶜ) := by
  classical
  obtain ⟨s,_,hs⟩ := Finset.exists_max_image Finset.univ r ⟨a,Finset.mem_univ _⟩
  have hmax (i : α) : r i ≤ r s := hs i (Finset.mem_univ _)
  let F : Fin (r s+1) → α := fun i ↦ R^[i.val] s
  have hF (i : Fin (r s+1)) : r (F i)=r s-i.val :=
    rank_iterate_before_root R a r hz hr s (by omega)
  have hFi : Function.Injective F := by
    intro i j heq
    have he := congrArg r heq
    rw [hF,hF] at he
    apply Fin.ext
    omega
  let f : Fin (r s+1) ↪ α := ⟨F,hFi⟩
  have hf (i : Fin (r s+1)) : r (f i)=r s-i.val := hF i
  have hnext (i : Fin (r s+1)) (hi : i.val+1 < r s+1) :
      R (f i)=f ⟨i.val+1,hi⟩ := by
    change R (R^[i.val] s)=R^[i.val+1] s
    rw [iterate_succ_apply']
  have hlast : f ⟨r s,by omega⟩=a := (hz _).mp (by rw [hf]; simp)
  have haS : a ∈ Set.range f := ⟨_,hlast⟩
  have houtside (i : α) (hi : i ∉ Set.range f) : i ≠ a := fun h ↦ hi (h ▸ haS)
  have hboundary (i : α) (hi : i ∉ Set.range f) (hRi : R i ∈ Set.range f) :
      ∃ B : Fin (r s+1), 0 < B.val ∧ R i=f B ∧
        ∃ d : Fin (r s+1), d.val+1=B.val ∧ R (f d)=R i ∧ f d ≠ a := by
    obtain ⟨B,hB⟩ := hRi
    have hri := hr i (houtside i hi)
    have hb := hf B
    have hm := hmax i
    have hBpos : 0 < B.val := by rw [hB] at hb; omega
    let d : Fin (r s+1) := ⟨B.val-1,by omega⟩
    have hdB : d.val+1=B.val := by dsimp [d]; omega
    refine ⟨B,hBpos,hB.symm,d,hdB,?_,?_⟩
    · rw [hnext d (by omega)]
      convert hB using 1
      congr 1
      exact Fin.ext hdB
    · intro heq
      have hd := hf d
      have ha0 := (hz _).mpr heq
      omega
  refine ⟨r s+1,by omega,f,?_,?_,hnext,?_,?_⟩
  · intro i; exact (hf i).trans (by omega)
  · intro i; have := hmax i; omega
  · intro i hi
    have he : i=⟨r s,by omega⟩ := Fin.ext (by change i.val=r s; omega)
    simpa only [he] using hlast
  · by_cases hsurj : Function.Surjective f
    · exact Or.inl hsurj
    · right
      obtain ⟨i,hi⟩ : ∃ i, i ∉ Set.range f := by simpa [Function.Surjective] using hsurj
      have hhit : ∃ t : ℕ, R^[t] i ∈ Set.range f := by
        refine ⟨r i,?_⟩
        have he : R^[r i] i=a := (hz _).mp (by
          rw [rank_iterate_before_root R a r hz hr i (le_refl _)]; simp)
        exact he ▸ haS
      let t := Nat.find hhit
      have ht : R^[t] i ∈ Set.range f := Nat.find_spec hhit
      have htpos : 0 < t := by
        by_contra h
        have ht0 : t=0 := by omega
        exact hi (by simpa [ht0] using ht)
      let c := R^[t-1] i
      have hc : c ∉ Set.range f := Nat.find_min hhit (by omega : t-1 < t)
      have hRc : R c ∈ Set.range f := by
        change R (R^[t-1] i) ∈ Set.range f
        rw [← iterate_succ_apply' R,show (t-1).succ=t by omega]
        exact ht
      obtain ⟨B,hB,hcB,d,hdB,hdc,hda⟩ := hboundary c hc hRc
      have hcd : c ≠ f d := fun he ↦ hc ⟨d,he.symm⟩
      have hcollision := hpair c (f d) (houtside c hc) hda hcd hdc.symm
      refine ⟨c,hc,B,hB,hcB,?_,?_⟩
      · intro j hj hjc hjR
        obtain ⟨D,_,_,e,_,hej,hea⟩ := hboundary j hj hjR
        have hje : j ≠ f e := fun he ↦ hj ⟨e,he.symm⟩
        rcases hcollision j (f e) (houtside j hj) hea hje hej.symm with he | he
        · exact hjc he
        · exact hj ⟨d,he.symm⟩
      · intro j hj k hk heq
        by_contra hne
        have hjc := (hcollision j k (houtside j hj) (houtside k hk) hne heq).resolve_right
          (fun he ↦ hj ⟨d,he.symm⟩)
        have hkc := (hcollision k j (houtside k hk) (houtside j hj) (Ne.symm hne) heq.symm).resolve_right
          (fun he ↦ hk ⟨d,he.symm⟩)
        exact hne (hjc.trans hkc.symm)

/-- The complement of the longest chain has its own extracted root rank. -/
theorem exists_rank_on_closed_complement
    {α : Type*} (R : α → α) (a : α) (r : α → ℕ)
    (hr : ∀ i, i ≠ a → r i=r (R i)+1)
    (S : Set α) (ha : a ∉ S) (c : S)
    (hclosed : ∀ i, i ∈ S → i ≠ c.val → R i ∈ S) :
    ∃ Q : S → S, (∀ i, i ≠ c → (Q i).val=R i.val) ∧
      (∀ i : S, r c.val ≤ r i.val) ∧
      (∀ i : S, r i.val-r c.val=0 ↔ i=c) ∧
      ∀ i : S, i ≠ c → r i.val-r c.val=(r (Q i).val-r c.val)+1 := by
  classical
  have hmin : ∀ t, ∀ i : S, r i.val=t → r c.val ≤ r i.val ∧ (r i.val=r c.val → i=c) := by
    intro t
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro i hi
      by_cases hic : i=c
      · subst i; exact ⟨le_refl _,fun _ ↦ rfl⟩
      have hia : i.val ≠ a := fun he ↦ ha (he ▸ i.property)
      have hiv : i.val ≠ c.val := fun he ↦ hic (Subtype.ext he)
      let j : S := ⟨R i.val,hclosed i.val i.property hiv⟩
      have hri := hr i.val hia
      have hj : r j.val < t := by change r (R i.val) < t; omega
      obtain ⟨hjmin,_⟩ := ih (r j.val) hj j rfl
      change r c.val ≤ r (R i.val) at hjmin
      exact ⟨by omega,fun he ↦ by omega⟩
  let Q : S → S := fun i ↦ if hi : i=c then c else
    ⟨R i.val,hclosed i.val i.property (fun he ↦ hi (Subtype.ext he))⟩
  have hQ (i : S) (hi : i ≠ c) : (Q i).val=R i.val := by simp [Q,hi]
  refine ⟨Q,hQ,fun i ↦ (hmin _ i rfl).1,?_,?_⟩
  · intro i
    obtain ⟨hle,heq⟩ := hmin _ i rfl
    constructor
    · intro h; exact heq (by omega)
    · intro h; subst i; omega
  · intro i hi
    have hia : i.val ≠ a := fun he ↦ ha (he ▸ i.property)
    have hri := hr i.val hia
    have hle := (hmin _ (Q i) rfl).1
    rw [hQ i hi] at hle ⊢
    omega

/-- Ordered actual doubling arrows give the expected powers of the
original first coordinate, without choosing a unit normalization. -/
theorem powers_of_ordered_doubling_arrows
    {L : ℕ} (hL : 0 < L) {G : Type*} [AddCommGroup G] (v : Fin L → G)
    (hd : ∀ i : Fin L, ∀ hi : i.val+1 < L, v ⟨i.val+1,hi⟩=2 • v i) :
    ∀ i : Fin L, v i=2^i.val • v ⟨0,hL⟩ := by
  intro i
  have aux : ∀ t, ∀ ht : t < L, v ⟨t,ht⟩=2^t • v ⟨0,hL⟩ := by
    intro t
    induction t with
    | zero => intro ht; simp
    | succ t ih =>
      intro ht
      rw [hd ⟨t,by omega⟩ ht,ih (by omega),← mul_nsmul,pow_succ]
  exact aux i.val i.isLt

/-- Every finite ranked one-escape doubling system with only one
possible collision pair is either one full chain or an ACTUAL merging
fork. The arm ordering is extracted by taking a longest main chain. -/
theorem exists_chain_or_fork_of_ranked_one_collision
    {α : Type*} [Fintype α] {G : Type*} [AddCommGroup G]
    (g : α → G) (R : α → α) (a : α) (r : α → ℕ)
    (hz : ∀ i, r i=0 ↔ i=a) (hr : ∀ i, i ≠ a → r i=r (R i)+1)
    (hd : ∀ i, i ≠ a → g (R i)=2 • g i)
    (hpair : ∀ u v, u ≠ a → v ≠ a → u ≠ v → R u=R v →
      ∀ i j, i ≠ a → j ≠ a → i ≠ j → R i=R j → i=u ∨ i=v) :
    (∃ L, 0 < L ∧ ∃ E : Fin L ≃ α, ∃ x : G, ∀ i, g (E i)=2^i.val • x) ∨
      ∃ A B L, 0 < A ∧ A ≤ B ∧ B < L ∧ ∃ E : Fin (A+L) ≃ α, ∃ x y : G,
        (∀ i : Fin A, g (E (Fin.castAdd L i))=2^i.val • x) ∧
        (∀ i : Fin L, g (E (Fin.natAdd A i))=2^i.val • y) ∧ 2^A • x=2^B • y := by
  classical
  obtain ⟨L,hL,f,hf,hmax,hnext,hlast,hcases⟩ :=
    exists_chain_and_injective_complement_of_ranked_one_collision R a r hz hr hpair
  have hmain : ∀ i : Fin L, g (f i)=2^i.val • g (f ⟨0,hL⟩) := by
    apply powers_of_ordered_doubling_arrows hL
    intro i hi
    rw [← hnext i hi,hd]
    intro he
    have h0 := (hz _).mpr he
    have hh := hf i
    omega
  rcases hcases with hsurj | ⟨c,hc,B,hB,hcB,hclosed,hinj⟩
  · exact Or.inl ⟨L,hL,Equiv.ofBijective f ⟨f.injective,hsurj⟩,_,hmain⟩
  · right
    let S : Set α := (Set.range f)ᶜ
    let c' : S := ⟨c,hc⟩
    have ha : a ∉ S := by
      intro h
      exact h ⟨⟨L-1,by omega⟩,hlast _ (by simp; omega)⟩
    obtain ⟨Q,hQ,hmin,hroot,hrank⟩ := exists_rank_on_closed_complement R a r hr S ha c' hclosed
    have hQi : ∀ i : S, i ≠ c' → ∀ j : S, j ≠ c' → Q i=Q j → i=j := by
      intro i hi j hj heq
      apply Subtype.ext
      apply hinj i.property j.property
      have he := congrArg Subtype.val heq
      rwa [hQ i hi,hQ j hj] at he
    obtain ⟨A,hA,γ,hγ,hγnext,hγlast⟩ := exists_full_chain_of_ranked_injective_map
      Q c' (fun i ↦ r i.val-r c) hroot hrank hQi
    have hcroot : r c=L-B.val := by
      have hca : c ≠ a := fun he ↦ ha (he ▸ hc)
      have hh := hr c hca
      rw [hcB,hf] at hh
      omega
    have hAB : A ≤ B.val := by
      have h0 := hγ ⟨0,hA⟩
      have hle := hmin (γ ⟨0,hA⟩)
      have hm := hmax (γ ⟨0,hA⟩).val
      change r (γ ⟨0,hA⟩).val-r c=A-1-0 at h0
      omega
    let join : S ⊕ Fin L → α := Sum.elim Subtype.val f
    have hjoin : Function.Bijective join := by
      constructor
      · rintro (i | i) (j | j) heq
        · exact congrArg Sum.inl (Subtype.ext heq)
        · exact False.elim (i.property ⟨j,heq.symm⟩)
        · exact False.elim (j.property ⟨i,heq⟩)
        · exact congrArg Sum.inr (f.injective heq)
      · intro i
        by_cases hi : i ∈ Set.range f
        · obtain ⟨j,rfl⟩ := hi
          exact ⟨Sum.inr j,rfl⟩
        · exact ⟨Sum.inl ⟨i,hi⟩,rfl⟩
    let E : Fin (A+L) ≃ α := finSumFinEquiv.symm.trans
      ((Equiv.sumCongr γ (Equiv.refl _)).trans (Equiv.ofBijective join hjoin))
    have hleft (i : Fin A) : E (Fin.castAdd L i)=(γ i).val := by simp [E,join]
    have hright (i : Fin L) : E (Fin.natAdd A i)=f i := by simp [E,join]
    have hside : ∀ i : Fin A, g (γ i).val=2^i.val • g (γ ⟨0,hA⟩).val := by
      apply powers_of_ordered_doubling_arrows hA
      intro i hi
      have hne : γ i ≠ c' := by
        intro he
        have hh := hγ i
        rw [he] at hh
        change r c-r c=A-1-i.val at hh
        omega
      rw [← hγnext i hi,hQ _ hne,hd]
      intro he
      exact ha (he ▸ (γ i).property)
    refine ⟨A,B.val,L,hA,hAB,B.isLt,E,g (γ ⟨0,hA⟩).val,g (f ⟨0,hL⟩),?_,?_,?_⟩
    · intro i; rw [hleft]; exact hside i
    · intro i; rw [hright]; exact hmain i
    · have hlastc : (γ ⟨A-1,by omega⟩).val=c :=
        congrArg Subtype.val (hγlast _ (by simp; omega))
      have hs := hside ⟨A-1,by omega⟩
      rw [hlastc] at hs
      have hca : c ≠ a := fun he ↦ ha (he ▸ hc)
      have hmerge := hd c hca
      rw [hcB,hmain,hs,← mul_nsmul,← pow_succ,show A-1+1=A by omega] at hmerge
      exact hmerge.symm

/-- Every finite map either admits a rootward rank, or has an actual
nonempty periodic block avoiding the proposed endpoint. -/
theorem rank_or_nonempty_cycle_avoiding_endpoint
    {α : Type*} [Fintype α] (R : α → α) (a : α) :
    (∃ r : α → ℕ, (∀ i, r i=0 ↔ i=a) ∧ ∀ i, i ≠ a → r i=r (R i)+1) ∨
      ∃ m, 0 < m ∧ ∃ e : Fin m ↪ α, ∃ P : Equiv.Perm (Fin m),
        (∀ i, e i ≠ a) ∧ ∀ i, e (P i)=R (e i) := by
  classical
  by_cases hhit : ∀ i, ∃ t : ℕ, R^[t] i=a
  · exact Or.inl (exists_rank_of_all_orbits_hit R a hhit)
  · right
    obtain ⟨i,hi⟩ : ∃ i, ∀ t : ℕ, R^[t] i ≠ a := by simpa using hhit
    let D : Set α := {j | ∀ t : ℕ, R^[t] j ≠ a}
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

/-- Actual cycle/chain/fork geometry is extracted from validity and
one-escape closure in any group with at most one nonzero involution.
Neither acyclicity, rank, injectivity nor a proposed decomposition is
assumed. -/
theorem exists_cycle_chain_or_fork_of_valid_one_escape
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g)
    {h : G} (hh : h+h=0) (hinv : ∀ u : G, u+u=0 → u=0 ∨ u=h)
    (a : Fin n) (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i) :
    (∃ m, 0 < m ∧ ∃ e : Fin m ↪ Fin n, ∃ P : Equiv.Perm (Fin m),
      ∀ i, g (e (P i))=2 • g (e i)) ∨
    (∃ L, 0 < L ∧ ∃ E : Fin L ≃ Fin n, ∃ x : G, ∀ i, g (E i)=2^i.val • x) ∨
      ∃ A B L, 0 < A ∧ A ≤ B ∧ B < L ∧ ∃ E : Fin (A+L) ≃ Fin n, ∃ x y : G,
        (∀ i : Fin A, g (E (Fin.castAdd L i))=2^i.val • x) ∧
        (∀ i : Fin L, g (E (Fin.natAdd A i))=2^i.val • y) ∧ 2^A • x=2^B • y := by
  classical
  let R : Fin n → Fin n := fun i ↦ if hi : i=a then a else Classical.choose (hclosed i hi)
  have hd (i : Fin n) (hi : i ≠ a) : g (R i)=2 • g i := by
    simpa only [R,dif_neg hi] using Classical.choose_spec (hclosed i hi)
  rcases rank_or_nonempty_cycle_avoiding_endpoint R a with ⟨r,hz,hr⟩ | ⟨m,hm,e,P,he,hP⟩
  · right
    apply exists_chain_or_fork_of_ranked_one_collision g R a r hz hr hd
    intro u v hua hva huv huvR i j hia hja hij hijR
    exact equal_double_collision_mem_pair_of_valid g hg hh hinv huv
      ((hd u hua).symm.trans ((congrArg g huvR).trans (hd v hva))) hij
      ((hd i hia).symm.trans ((congrArg g hijR).trans (hd j hja)))
  · exact Or.inl ⟨m,hm,e,P,fun i ↦ by rw [hP,hd _ (he i)]⟩

/-- Any embedded actual cycle, even a singleton, excludes a one-escape
exceptional tuple in dimensions at least four. The singleton cutoff is
extracted from the same general outsider bound. -/
theorem not_validTuple_exceptional_of_one_escape_embedded_cycle
    {n m : ℕ} (hn : 4 ≤ n) (hm : 0 < m) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (a : Fin n)
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i)
    (e : Fin m ↪ Fin n) (P : Equiv.Perm (Fin m))
    (hcycle : ∀ i, g (e (P i))=2 • g (e i)) : ¬ ValidTuple g := by
  intro hg
  have hmn : m ≤ n := by simpa using Fintype.card_le_of_injective _ e.injective
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hmn
  obtain ⟨E,hE⟩ := Equiv.Perm.exists_extending_pair (Fin.castAdd k) e
    (Fin.castAdd_injective m k) e.injective
  have hc : ∀ i, i ≠ a → ∃ j, g j=2 • g i+0 := by simpa only [add_zero] using hclosed
  have hd : ∀ i, g (E (Fin.castAdd k (P i)))=2 • g (E (Fin.castAdd k i))+0 := by
    simpa only [hE,add_zero] using hcycle
  by_cases hm2 : 2 ≤ m
  · exact not_validTuple_exceptional_of_one_escape_affine_cycle hm2 hnpow g a 0 hc E P hd hg
  · have hB : 2 ≤ globalBound (m+k-1) := (nmin_eq (by omega : 2 ≤ m+k-1)).1.1
    letI : NeZero (2*globalBound (m+k-1)) := ⟨by omega⟩
    have hsize := outside_le_cycle_add_one_of_valid_one_escape_affine_cycle hm g hg a 0 hc E P hd
    omega

/-- Complete G3 exclusion for ALL one-escape affine-doubling tuples.
All cycle/chain/fork geometry is extracted from the actual parent. -/
theorem not_validTuple_exceptional_of_one_escape_affine_doubling
    {n : ℕ} (hn : 3 ≤ n) (hnpow : 2^Nat.log 2 n ≠ n)
    (g : Fin n → ZMod (2*globalBound (n-1))) (a : Fin n)
    (b : ZMod (2*globalBound (n-1)))
    (hclosed : ∀ i, i ≠ a → ∃ j, g j=2 • g i+b) : ¬ ValidTuple g := by
  intro hg
  by_cases hn4 : 4 ≤ n
  · have hB : 2 ≤ globalBound (n-1) := (nmin_eq (by omega : 2 ≤ n-1)).1.1
    letI : NeZero (2*globalBound (n-1)) := ⟨by omega⟩
    let u : Fin n → ZMod (2*globalBound (n-1)) := fun i ↦ g i+b
    have hu : ValidTuple u := by
      simpa only [u,sub_neg_eq_add] using validTuple_sub_const g hg (-b)
    have hc : ∀ i, i ≠ a → ∃ j, u j=2 • u i := by
      intro i hi
      obtain ⟨j,hj⟩ := hclosed i hi
      refine ⟨j,?_⟩
      simp only [u,hj,two_nsmul]
      abel
    have hgap : 2*globalBound (n-1) < globalBound n := by
      have hp : 2^Nat.log 2 ((n-1)+1) ≠ (n-1)+1 := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using hnpow
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using
        two_mul_globalBound_lt_succ_of_not_power (by omega : 2 ≤ n-1) hp
    rcases exists_cycle_chain_or_fork_of_valid_one_escape u hu (half_add_half rfl)
      (fun x hx ↦ zmod_eq_zero_or_half_of_add_self_eq_zero rfl x hx) a hc with
      ⟨m,hm,e,P,hcycle⟩ | ⟨L,hL,E,x,hchain⟩ | ⟨A,B,L,hA,hAB,hBL,E,x,y,hleft,hright,hmerge⟩
    · exact not_validTuple_exceptional_of_one_escape_embedded_cycle hn4 hm hnpow u a hc e P hcycle hu
    · have hLn : L=n := by simpa using Fintype.card_congr E
      subst L
      have hv := validTuple_embedding E.toEmbedding u hu
      have hf := valid_fixed_of_valid_doubling_chain _ hv x hchain
      have hb := (nmin_eq (by omega : 2 ≤ n)).2 ⟨by omega,hf⟩
      change globalBound n ≤ 2*globalBound (n-1) at hb
      omega
    · have hAn : A+L=n := by simpa using Fintype.card_congr E
      subst n
      exact not_validTuple_exceptional_of_actual_fork hA hAB hBL hnpow u E 0 x y
        (by simpa only [add_zero] using hleft) (by simpa only [add_zero] using hright) hmerge hu
  · have hn3 : n=3 := by omega
    subst n
    have hv : ValidTuple (g : Fin 3 → ZMod 4) := by
      simpa only [globalBound,show Nat.log 2 (3-1)=1 by decide] using hg
    have he := equality_order_two (m := 2) (G := ZMod 4) g hv (by norm_num [ZMod.card]) (1 : ZMod 4)
    exact (by decide : 2 • (1 : ZMod 4) ≠ 0) he

end MinModulus
