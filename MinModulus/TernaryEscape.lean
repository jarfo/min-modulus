import MinModulus.TernaryForest
import MinModulus.TriplingClosure


/-!
# Unconditional affine-tripling escape bounds at odd moduli

The periodic part of an embedded actual tripling map has one orbit by
validity and injective doubling. One mark therefore makes every orbit hit
the terminal set. At odd cyclic moduli, one further mark removes the only
possible tripling collision pair. The resulting forest retains every
original coordinate and requires no injectivity or acyclicity assumption.
Applying parity-colored ternary packing bounds the genuine escape count
of every affine tripling map, with no conjectural input or finite cutoff.
-/

namespace MinModulus
open Finset Function

/-- A tripling permutation of a valid tuple is transitive, including
singletons, in a group with injective doubling. -/
theorem exists_iterate_eq_of_valid_tripling_perm
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G,x+x=y+y → x=y)
    (g : Fin n → G) (hg : ValidTuple g)
    (R : Equiv.Perm (Fin n)) (hd : ∀ i,g (R i)=3 • g i)
    (a b : Fin n) : ∃ k : ℕ,R^[k] a=b := by
  by_cases hn : 2 ≤ n
  · have hcycle := isCycle_of_valid_tripling hn hinj g hg R hd
    have hab : R.SameCycle a b :=
      ((Equiv.Perm.isCycle_iff_sameCycle (tripling_apply_ne_of_valid hn hinj g hg R hd a)).mp
        hcycle).mpr (tripling_apply_ne_of_valid hn hinj g hg R hd b)
    exact hab.exists_nat_pow_eq
  · refine ⟨0,?_⟩
    simp only [iterate_zero_apply]
    apply Fin.ext
    omega

/-- The periodic part of any embedded actual tripling map has one orbit.
The surrounding valid tuple need not itself be tripling closed. -/
theorem exists_iterate_eq_of_embedded_valid_tripling_periodic
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G,x+x=y+y → x=y)
    (g : Fin n → G) (hg : ValidTuple g)
    {α : Type*} [Fintype α] (emb : α ↪ Fin n) (R : α → α)
    (hd : ∀ i,g (emb (R i))=3 • g (emb i))
    {a b : α} (ha : a ∈ periodicPts R) (hb : b ∈ periodicPts R) :
    ∃ k : ℕ,R^[k] a=b := by
  classical
  let P := periodicPts R
  let d := Fintype.card P
  let e : Fin d ≃ P := (Fintype.equivFin P).symm
  let p : Equiv.Perm P := (bijOn_periodicPts R).equiv R
  let r : Equiv.Perm (Fin d) := e.trans (p.trans e.symm)
  let f : Fin d ↪ α := e.toEmbedding.trans (Function.Embedding.subtype P)
  have hconj : ∀ i,f (r i)=R (f i) := by
    intro i
    simp [f,r,p,Set.BijOn.equiv]
    rfl
  have hv : ValidTuple (fun i ↦ g (emb (f i))) := validTuple_embedding (f.trans emb) g hg
  have hd' : ∀ i,g (emb (f (r i)))=3 • g (emb (f i)) := by
    intro i
    rw [hconj,hd]
  obtain ⟨k,hk⟩ := exists_iterate_eq_of_valid_tripling_perm hinj
    (fun i ↦ g (emb (f i))) hv r hd' (e.symm ⟨a,ha⟩) (e.symm ⟨b,hb⟩)
  have hiter : ∀ k i,f (r^[k] i)=R^[k] (f i) := by
    intro k
    induction k with
    | zero => intro i; rfl
    | succ k ih =>
      intro i
      rw [iterate_succ_apply',hconj,ih,iterate_succ_apply']
  refine ⟨k,?_⟩
  have heq := congrArg f hk
  rw [hiter] at heq
  have hea : f (e.symm ⟨a,ha⟩)=a := by
    change (e (e.symm ⟨a,ha⟩)).val=a
    rw [e.apply_symm_apply]
  have heb : f (e.symm ⟨b,hb⟩)=b := by
    change (e (e.symm ⟨b,hb⟩)).val=b
    rw [e.apply_symm_apply]
  simpa only [hea,heb] using heq

/-- One additional marked vertex makes every orbit of an actual partial
tripling map reach the marked set. No injectivity of tripling is required. -/
theorem exists_rank_after_one_tripling_cycle_mark
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (hinj : ∀ x y : G,x+x=y+y → x=y)
    (g : Fin n → G) (hg : ValidTuple g)
    (R : Fin n → Fin n) (A : Finset (Fin n))
    (hd : ∀ i,i ∉ A → g (R i)=3 • g i) :
    ∃ B : Finset (Fin n),A ⊆ B ∧ B.card ≤ A.card+1 ∧
      ∃ r : Fin n → ℕ,(∀ i,r i=0 ↔ i ∈ B) ∧
        ∀ i,i ∉ B → r i=r (R i)+1 := by
  classical
  by_cases hhit : ∀ i,∃ t : ℕ,R^[t] i ∈ A
  · obtain ⟨r,hz,hr⟩ := exists_rank_of_all_orbits_hit_set R (↑A : Set (Fin n)) hhit
    exact ⟨A,by rfl,by omega,r,hz,hr⟩
  · obtain ⟨i,hi⟩ : ∃ i,∀ t : ℕ,R^[t] i ∉ A := by simpa using hhit
    let D : Set (Fin n) := {j | ∀ t : ℕ,R^[t] j ∉ A}
    letI : Fintype D := Fintype.ofFinite D
    let embD : D ↪ Fin n := ⟨fun z ↦ z.val,fun _ _ h ↦ Subtype.ext h⟩
    let T : D → D := fun j ↦ ⟨R j.val,fun t ht ↦ j.property (t+1) (by
      rw [iterate_succ_apply]; exact ht)⟩
    have hiter : ∀ k (j : D),(T^[k] j).val=R^[k] j.val := by
      intro k
      induction k with
      | zero => intro j; rfl
      | succ k ih => intro j; rw [iterate_succ_apply',iterate_succ_apply']; exact congrArg R (ih j)
    have htriple (j : D) : g (T j).val=3 • g j.val := hd j.val (j.property 0)
    obtain ⟨k,hk⟩ := exists_periodic_iterate_finite T (⟨i,hi⟩ : D)
    let a : D := T^[k] ⟨i,hi⟩
    have ha : a ∈ periodicPts T := hk
    let B := insert a.val A
    have hhitB : ∀ j,∃ t : ℕ,R^[t] j ∈ B := by
      intro j
      by_cases hj : ∃ t : ℕ,R^[t] j ∈ A
      · obtain ⟨t,ht⟩ := hj
        exact ⟨t,Finset.mem_insert_of_mem ht⟩
      · have hj' : ∀ t : ℕ,R^[t] j ∉ A := by simpa using hj
        let j' : D := ⟨j,hj'⟩
        obtain ⟨l,hl⟩ := exists_periodic_iterate_finite T j'
        obtain ⟨s,hs⟩ := exists_iterate_eq_of_embedded_valid_tripling_periodic hinj
          g hg embD T htriple hl ha
        refine ⟨s+l,?_⟩
        have hh : R^[s] (R^[l] j)=a.val := by
          calc
            _=R^[s] (T^[l] j').val := congrArg (R^[s]) (hiter l j').symm
            _=(T^[s] (T^[l] j')).val := (hiter s (T^[l] j')).symm
            _=a.val := congrArg (fun z : D ↦ z.val) hs
        rw [iterate_add_apply]
        exact Finset.mem_insert.mpr (Or.inl hh)
    obtain ⟨r,hz,hr⟩ := exists_rank_of_all_orbits_hit_set R (↑B : Set (Fin n)) hhitB
    exact ⟨B,Finset.subset_insert _ _,by dsimp only [B]; exact Finset.card_insert_le _ _,r,hz,hr⟩

/-- A first-hit rank and injectivity away from the terminals give a
complete actual ternary forest. Terminal values of the map are irrelevant. -/
theorem exists_ternary_forest_of_ranked_partial_tripling
    {α : Type*} [Fintype α] {G : Type*} [AddCommGroup G]
    (g : α → G) (R : α → α) (A : Finset α) (r : α → ℕ)
    (hz : ∀ i,r i=0 ↔ i ∈ A) (hr : ∀ i,i ∉ A → r i=r (R i)+1)
    (hinj : ∀ i,i ∉ A → ∀ j,j ∉ A → R i=R j → i=j)
    (hd : ∀ i,i ∉ A → g (R i)=3 • g i) :
    ∃ L : A → ℕ,(∀ a,0 < L a) ∧ (∑ a,L a)=Fintype.card α ∧
      ∃ E : (Σ a : A,Fin (L a)) ≃ α,∃ x : A → G,
      (∀ a (i : Fin (L a)),g (E ⟨a,i⟩)=3^i.val • x a) ∧
      (∀ a (i : Fin (L a)),i.val+1=L a → E ⟨a,i⟩=a.val) := by
  classical
  let Q : α → α := fun i ↦ if i ∈ A then i else R i
  have hfix : ∀ i,i ∈ A → Q i=i := by intro i hi; simp only [Q,if_pos hi]
  have hsame : ∀ i,i ∉ A → Q i=R i := by intro i hi; simp only [Q,if_neg hi]
  have hrQ : ∀ i,i ∉ A → r i=r (Q i)+1 := by
    intro i hi
    rw [hsame i hi]
    exact hr i hi
  have hQi : ∀ i,i ∉ A → ∀ j,j ∉ A → Q i=Q j → i=j := by
    intro i hi j hj he
    rw [hsame i hi,hsame j hj] at he
    exact hinj i hi j hj he
  obtain ⟨L,hL,E,hEr,hEa,hEe⟩ := exists_full_chain_forest_of_ranked_injective_map Q A hfix r hz hrQ hQi
  have hcard : (∑ a,L a)=Fintype.card α := by
    simpa only [Fintype.card_sigma,Fintype.card_fin] using Fintype.card_congr E
  let x : A → G := fun a ↦ g (E ⟨a,⟨0,hL a⟩⟩)
  refine ⟨L,hL,hcard,E,x,?_,hEe⟩
  intro a
  apply powers_of_ordered_tripling_arrows (hL a)
  intro i hi
  have hnot : E ⟨a,i⟩ ∉ A := by
    intro h
    have h0 := (hz _).mpr h
    have hh := hEr a i
    omega
  rw [← hEa a i hi,hsame _ hnot,hd _ hnot]

/-- At an odd cyclic modulus, marking at most one source removes all
tripling collisions among the remaining coordinates of a valid tuple. -/
theorem exists_small_tripling_collision_cover
    {n N : ℕ} (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g) :
    ∃ C : Finset (Fin n),C.card ≤ 1 ∧
      ∀ i,i ∉ C → ∀ j,j ∉ C → 3 • g i=3 • g j → i=j := by
  classical
  by_cases h3 : 3 ∣ N
  · obtain ⟨M,rfl⟩ := h3
    have hM : Odd M := (Nat.odd_mul.mp hN).2
    letI : NeZero M := ⟨hM.pos.ne'⟩
    by_cases hi : Function.Injective (fun i ↦ 3 • g i)
    · exact ⟨∅,by simp,fun i _ j _ he ↦ hi he⟩
    obtain ⟨a,b,he,hab⟩ : ∃ a b,3 • g a=3 • g b ∧ a≠b := by
      simpa [Function.Injective] using hi
    refine ⟨{a},by simp,?_⟩
    intro i hi j hj hij
    by_contra hne
    have hia : i≠a := by simpa only [Finset.mem_singleton] using hi
    have hja : j≠a := by simpa only [Finset.mem_singleton] using hj
    have hib : i=b := (tripling_collision_mem_pair_of_valid_zmod hM g hg hab he hne hij).resolve_left hia
    have hjb : j=b := (tripling_collision_mem_pair_of_valid_zmod hM g hg hab he (Ne.symm hne) hij.symm).resolve_left hja
    exact hne (hib.trans hjb.symm)
  · have hcop : Nat.Coprime 3 N := (Nat.Prime.coprime_iff_not_dvd (by decide)).mpr h3
    have hunit : IsUnit ((3:ℕ) : ZMod N) := (ZMod.isUnit_iff_coprime 3 N).mpr hcop
    refine ⟨∅,by simp,?_⟩
    intro i _ j _ he
    apply validTuple_injective g hg
    apply hunit.mul_left_cancel
    simpa only [nsmul_eq_mul] using he

/-- Every valid odd-cyclic tuple with a partial tripling map has a complete
actual ternary forest after at most two additional marks. No coordinate is
removed, and no injectivity or absence of cycles is assumed. -/
theorem exists_ternary_forest_with_two_additional_marks
    {n N : ℕ} (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (A : Finset (Fin n)) (hclosed : ∀ i,i ∉ A → ∃ j,g j=3 • g i) :
    ∃ B : Finset (Fin n),A ⊆ B ∧ B.card ≤ A.card+2 ∧
      ∃ L : B → ℕ,(∀ a,0 < L a) ∧ (∑ a,L a)=n ∧
      ∃ E : (Σ a : B,Fin (L a)) ≃ Fin n,∃ x : B → ZMod N,
      (∀ a (i : Fin (L a)),g (E ⟨a,i⟩)=3^i.val • x a) ∧
      (∀ a (i : Fin (L a)),i.val+1=L a → E ⟨a,i⟩=a.val) := by
  classical
  letI : NeZero N := ⟨hN.pos.ne'⟩
  obtain ⟨C,hC,hCi⟩ := exists_small_tripling_collision_cover hN g hg
  let S := A ∪ C
  have hAS : A ⊆ S := Finset.subset_union_left
  have hCS : C ⊆ S := Finset.subset_union_right
  have hScard : S.card ≤ A.card+1 := by
    have hh := Finset.card_union_le A C
    change S.card ≤ A.card+C.card at hh
    omega
  have hclosedS : ∀ i,i ∉ S → ∃ j,g j=3 • g i :=
    fun i hi ↦ hclosed i (fun ha ↦ hi (hAS ha))
  let R : Fin n → Fin n := fun i ↦ if hi : i ∈ S then i else Classical.choose (hclosedS i hi)
  have hd : ∀ i,i ∉ S → g (R i)=3 • g i := by
    intro i hi
    simpa only [R,dif_neg hi] using Classical.choose_spec (hclosedS i hi)
  have hRi : ∀ i,i ∉ S → ∀ j,j ∉ S → R i=R j → i=j := by
    intro i hi j hj he
    apply hCi i (fun hc ↦ hi (hCS hc)) j (fun hc ↦ hj (hCS hc))
    rw [← hd i hi,← hd j hj,he]
  obtain ⟨B,hSB,hB,r,hz,hr⟩ :=
    exists_rank_after_one_tripling_cycle_mark (add_self_injective_zmod hN) g hg R S hd
  have hnot (i) (hi : i ∉ B) : i ∉ S := fun hs ↦ hi (hSB hs)
  obtain ⟨L,hL,hsize,E,x,hchain,hend⟩ := exists_ternary_forest_of_ranked_partial_tripling g R B r hz hr
    (fun i hi j hj he ↦ hRi i (hnot i hi) j (hnot j hj) he)
    (fun i hi ↦ hd i (hnot i hi))
  refine ⟨B,hAS.trans hSB,by omega,L,hL,?_,E,x,hchain,hend⟩
  simpa only [Fintype.card_fin] using hsize

/-- The stars-and-bars corner grows monotonically with the number of arms. -/
theorem ternary_corner_card_mono {n r s : ℕ} (hn : 0 < n) (hrs : r ≤ s) :
    (n+r-1).choose r ≤ (n+s-1).choose s := by
  have heq (k : ℕ) : (n+k-1).choose k=(n+k-1).choose (n-1) := by
    have hh := Nat.choose_symm (show k ≤ n+k-1 by omega)
    have hsub : n+k-1-k=n-1 := by omega
    rw [hsub] at hh
    exact hh.symm
  rw [heq,heq]
  exact Nat.choose_le_choose _ (by omega)

/-- The complete ternary-forest bound grows with the marked escape budget. -/
theorem ternary_forest_bound_mono {n r s K : ℕ} (hn : 0 < n) (hrs : r ≤ s) :
    2^(r+1)*K+2^r*(n+r-1).choose r ≤
      2^(s+1)*K+2^s*(n+s-1).choose s := by
  apply Nat.add_le_add
  · exact Nat.mul_le_mul_right K (Nat.pow_le_pow_right (by decide) (by omega))
  · exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) hrs) (ternary_corner_card_mono hn hrs)

/-- An unconditional escape-count bound for every affine tripling map
on a valid tuple at an odd cyclic modulus. Two additional marks pay for
possible tripling collisions and the periodic component. -/
theorem exponential_bound_of_valid_odd_affine_tripling
    {n N : ℕ} (hn : 0 < n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g)
    (A : Finset (Fin n)) (c : ZMod N)
    (hclosed : ∀ i,i ∉ A → ∃ j,g j=3 • g i+c) :
    3^n ≤ 2^(A.card+3)*N+
      2^(A.card+2)*(n+A.card+1).choose (A.card+2) := by
  letI : NeZero N := ⟨hN.pos.ne'⟩
  obtain ⟨b,hb⟩ := (Finite.surjective_of_injective
    (f := fun x : ZMod N ↦ x+x) (add_self_injective_zmod hN)) c
  let u : Fin n → ZMod N := fun i ↦ g i-(-b)
  have hu : ValidTuple u := validTuple_sub_const g hg (-b)
  have huc : ∀ i,i ∉ A → ∃ j,u j=3 • u i := by
    intro i hi
    obtain ⟨j,hj⟩ := hclosed i hi
    refine ⟨j,?_⟩
    dsimp only [u]
    rw [hj,← hb]
    simp only [three_nsmul]
    abel
  obtain ⟨B,_,hB,L,_,_,E,x,hchain,_⟩ := exists_ternary_forest_with_two_additional_marks hN u hu A huc
  have hbound := ternary_forest_exponential_card_bound hn L u hu E x 0
    (by simpa only [add_zero] using hchain)
  simp only [Fintype.card_coe,ZMod.card] at hbound
  have hmono := ternary_forest_bound_mono (K:=N) hn hB
  have hadd : n+(A.card+2)-1=n+A.card+1 := by omega
  have hexp : A.card+2+1=A.card+3 := by omega
  simpa only [hadd,hexp] using hbound.trans hmono

/-- The unconditional bound applies directly to the genuine escapes of
any affine tripling map; no terminal set is supplied as an assumption. -/
theorem exponential_bound_of_genuine_affine_tripling_escapes
    {n N : ℕ} (hn : 0 < n) (hN : Odd N)
    (g : Fin n → ZMod N) (hg : ValidTuple g) (c : ZMod N) :
    let A := Finset.univ.filter (fun i ↦ ∀ j,g j≠3 • g i+c)
    3^n ≤ 2^(A.card+3)*N+
      2^(A.card+2)*(n+A.card+1).choose (A.card+2) := by
  classical
  dsimp only
  apply exponential_bound_of_valid_odd_affine_tripling hn hN g hg _ c
  intro i hi
  have hh : ¬ ∀ j,g j≠3 • g i+c := by simpa only [Finset.mem_filter,Finset.mem_univ,true_and] using hi
  simpa using hh

end MinModulus
