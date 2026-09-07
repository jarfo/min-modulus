import MinModulus.TwoHoleFibreChain

/-!
# Arbitrary quotient holes and a uniform actual-chain budget

Finite partial injections extend to actual permutations. Subset-sum
injectivity forces every orbit to hit an exception, and its first-hit
segment is an actual injective doubling chain. Endpoint/time labels
then give a uniform exception-count bound. Beside an actual cycle,
thin-cover lifting bounds every path by floor(log2(2*m)).

At any odd subgroup index d, the actual full-cover rival rule allows
at most d-2^k exceptional doubles, so k <= (d-2^k)*floor(log2(2*m)).
This holds for every actual affine cycle, not just majority cycles or
a prescribed number of holes. A direct arithmetic consumer gives the
stronger binary bound wherever all possible subbinary odd indices
violate the budget. Arbitrary critical structure remains unextracted.
-/

namespace MinModulus
open Finset

/-- Extend any injective finite partial map to an actual permutation.
The exceptional set may have arbitrary size. -/
theorem exists_perm_eq_on_finset_of_injOn
    {α : Type*} [DecidableEq α] (S : Finset α) (f : α → α)
    (hi : Set.InjOn f S) : ∃ P : Equiv.Perm α, ∀ i ∈ S, P i=f i := by
  classical
  let F : ↥S → ↥(S.image f) := fun i ↦ ⟨f i,Finset.mem_image.mpr ⟨i,i.property,rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro i j heq
      apply Subtype.ext
      exact hi i.property j.property (congrArg Subtype.val heq)
    · intro j
      obtain ⟨i,hiS,hij⟩ := Finset.mem_image.mp j.property
      exact ⟨⟨i,hiS⟩,Subtype.ext hij⟩
  let E : ↥S ≃ ↥(S.image f) := Equiv.ofBijective F hF
  refine ⟨E.extendSubtype,?_⟩
  intro i hiS
  rw [Equiv.extendSubtype_apply_of_mem E i hiS]
  rfl

/-- Every permutation orbit following doubling outside an arbitrary
exception set reaches that set when the coordinate subset cube is
injective. Otherwise the orbit itself would be a nonempty zero-sum subset. -/
theorem exists_pow_mem_exceptions_of_partial_doubling_perm
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (q : Fin n → G)
    (hi : Function.Injective (fun S : Finset (Fin n) ↦ ∑ i ∈ S, q i))
    (P : Equiv.Perm (Fin n)) (B : Finset (Fin n))
    (hd : ∀ i, i ∉ B → q (P i)=2 • q i) (a : Fin n) :
    ∃ r : ℕ, (P^r) a ∈ B := by
  classical
  let C : Finset (Fin n) := Finset.univ.filter (P.SameCycle a)
  have ha : a ∈ C := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Equiv.Perm.SameCycle.refl P a⟩
  have hCmem (i : Fin n) : P i ∈ C ↔ i ∈ C := by simp [C]
  have hCcycle : P.IsCycleOn (C : Set (Fin n)) := by
    refine ⟨P.bijOn hCmem,?_⟩
    intro i hiC j hjC
    have hai : P.SameCycle a i := (Finset.mem_filter.mp hiC).2
    have haj : P.SameCycle a j := (Finset.mem_filter.mp hjC).2
    exact hai.symm.trans haj
  have hex : ∃ b ∈ C, b ∈ B := by
    by_contra hnot
    have havoid (i : Fin n) (hiC : i ∈ C) : i ∉ B := fun hiB ↦ hnot ⟨i,hiC,hiB⟩
    have hsum : (∑ i ∈ C, q (P i))=∑ i ∈ C, q i :=
      Finset.sum_bij (fun i _ ↦ P i) (fun i hiC ↦ (hCmem i).mpr hiC)
        (fun _ _ _ _ hij ↦ P.injective hij)
        (fun j hj ↦ by obtain ⟨i,hiC,hij⟩ := hCcycle.1.surjOn hj; exact ⟨i,hiC,hij⟩)
        (fun _ _ ↦ rfl)
    have heq : (∑ i ∈ C, q (P i))=2 • (∑ i ∈ C, q i) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun i hiC ↦ hd i (havoid i hiC))
    rw [heq,two_nsmul] at hsum
    have hz : (∑ i ∈ C, q i)=0 := by
      apply add_right_cancel (b := ∑ i ∈ C, q i)
      simpa only [zero_add] using hsum
    have hempty : C=∅ := hi (by simpa only [Finset.sum_empty] using hz)
    simp [hempty] at ha
  obtain ⟨b,hbC,hbB⟩ := hex
  obtain ⟨r,_,hr⟩ := hCcycle.exists_pow_eq ha hbC
  exact ⟨r,hr ▸ hbB⟩

/-- The initial segment ending at the first exception is an ACTUAL
injective doubling chain, with its original endpoint and length exposed. -/
theorem exists_chain_to_exception_of_partial_doubling_perm
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (q : Fin n → G)
    (hi : Function.Injective (fun S : Finset (Fin n) ↦ ∑ i ∈ S, q i))
    (P : Equiv.Perm (Fin n)) (B : Finset (Fin n))
    (hd : ∀ i, i ∉ B → q (P i)=2 • q i) (a : Fin n) :
    ∃ r : ℕ, (P^r) a ∈ B ∧ (∀ t < r, (P^t) a ∉ B) ∧
      Function.Injective (fun i : Fin (r+1) ↦ (P^i.val) a) ∧
      ∀ i : Fin (r+1), q ((P^i.val) a)=2^i.val • q a := by
  classical
  have hex := exists_pow_mem_exceptions_of_partial_doubling_perm q hi P B hd a
  let r := Nat.find hex
  have hr : (P^r) a ∈ B := Nat.find_spec hex
  have hmin (t : ℕ) (ht : t < r) : (P^t) a ∉ B := Nat.find_min hex ht
  refine ⟨r,hr,hmin,?_,?_⟩
  · intro i j hij
    apply Fin.ext
    by_contra hne
    wlog hlt : i.val < j.val generalizing i j
    · exact this (i := j) (j := i) hij.symm (Ne.symm hne) (by omega)
    have he := congrArg (fun z ↦ (P^(r-j.val)) z) hij
    simp only [← Equiv.Perm.mul_apply,← pow_add] at he
    have hleft : r-j.val+i.val < r := by omega
    have hright : r-j.val+j.val=r := by omega
    rw [hright] at he
    exact hmin _ hleft (he.symm ▸ hr)
  · have hp (t : ℕ) (ht : t ≤ r) : q ((P^t) a)=2^t • q a := by
      induction t with
      | zero => simp
      | succ t ih =>
        rw [pow_succ',Equiv.Perm.mul_apply,hd _ (hmin t (by omega)),ih (by omega),pow_succ',mul_smul]
    exact fun i ↦ hp i.val (by omega)

/-- Bounded hitting times for a permutation inject all coordinates
into exception endpoints times time labels. The exception set and
time bound are arbitrary, not a fixed one- or two-hole case. -/
theorem card_le_exceptions_mul_of_bounded_perm_hits
    {n L : ℕ} (P : Equiv.Perm (Fin n)) (B : Finset (Fin n))
    (hhit : ∀ a, ∃ r < L, (P^r) a ∈ B) : n ≤ B.card*L := by
  classical
  let r : Fin n → ℕ := fun a ↦ Classical.choose (hhit a)
  have hr (a : Fin n) : r a < L ∧ (P^(r a)) a ∈ B := Classical.choose_spec (hhit a)
  let F : Fin n → ↥B × Fin L := fun a ↦ (⟨(P^(r a)) a,(hr a).2⟩,⟨r a,(hr a).1⟩)
  have hF : Function.Injective F := by
    intro a b hab
    have htime : r a=r b := congrArg (fun z : ↥B × Fin L ↦ z.2.val) hab
    have hend : (P^(r a)) a=(P^(r b)) b := congrArg (fun z : ↥B × Fin L ↦ z.1.val) hab
    rw [← htime] at hend
    exact (P^(r a)).injective hend
  have hc := Fintype.card_le_of_injective F hF
  simpa only [Fintype.card_fin,Fintype.card_prod,Fintype.card_coe] using hc

/-- Beside an actual cycle, an arbitrary exception set in outside
quotient doubling must be large enough to terminate all the short
actual chains. This bounds ALL exception counts in one theorem. -/
theorem outside_card_le_exceptions_mul_log_of_valid_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero (2^m-1)] [NeZero (d*(2^m-1))]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ j ∈ S,
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m j))))
    (P : Equiv.Perm (Fin k)) (B : Finset (Fin k))
    (hd : ∀ i, i ∉ B →
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m (P i)))=
        2 • ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i))) :
    k ≤ B.card*Nat.log 2 (2*m) := by
  classical
  let q : Fin k → ZMod d := fun i ↦
    ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i))
  apply card_le_exceptions_mul_of_bounded_perm_hits P B
  intro a
  obtain ⟨r,hr,_,hpath,hchain⟩ := exists_chain_to_exception_of_partial_doubling_perm q hi P B hd a
  let path : Fin (r+1) ↪ Fin k := ⟨fun i ↦ (P^i.val) a,hpath⟩
  let f : Fin (m+(r+1)) ↪ Fin (m+k) := finSumFinEquiv.symm.toEmbedding.trans
    (((Function.Embedding.refl (Fin m)).sumMap path).trans finSumFinEquiv.toEmbedding)
  have hleft (i : Fin m) : f (Fin.castAdd (r+1) i)=Fin.castAdd k i := by simp [f]
  have hright (i : Fin (r+1)) : f (Fin.natAdd m i)=Fin.natAdd m ((P^i.val) a) := by simp [f,path]
  have hbound := two_pow_outside_le_length_of_valid_mapped_cycle_quotient_chain hm τ hτ
    (fun i ↦ g (f i)) (validTuple_embedding f g hg)
    (by intro i; rw [hleft,hpref]) (Equiv.refl _) (q a)
    (by intro i; simpa only [Equiv.refl_apply,hright,q] using hchain i)
  have hlinear := two_mul_le_two_pow (r+1)
  have hrm : r+1 ≤ m := by omega
  have hpow : 2^(r+1) ≤ 2*m := by omega
  have hlog : r+1 ≤ Nat.log 2 (2*m) :=
    (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr hpow
  exact ⟨r,by omega,hr⟩

/-- In an odd cyclic quotient, arbitrary cube holes account for an
exception set of at most the same size in an ACTUAL doubling permutation.
The represented-double condition is the general actual-fibre rival rule. -/
theorem exists_partial_doubling_perm_with_card_le_cube_holes
    {k d : ℕ} (hd : Odd d) (q : Fin k → ZMod d)
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i))
    (hrep : ∀ i, (∃ S : Finset (Fin k), (∑ j ∈ S, q j)=2 • q i) →
      2 • q i=0 ∨ ∃ j, q j=2 • q i) :
    ∃ P : Equiv.Perm (Fin k), ∃ B : Finset (Fin k), B.card ≤ d-2^k ∧
      ∀ i, i ∉ B → q (P i)=2 • q i := by
  classical
  letI : NeZero d := ⟨hd.pos.ne'⟩
  let C : Finset (ZMod d) := Finset.univ.image (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i)
  let B : Finset (Fin k) := Finset.univ.filter (fun i ↦ 2 • q i ∉ C)
  have hCcard : C.card=2^k := by
    simp only [C,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_finset,Fintype.card_fin]
  have hqi : Function.Injective q := by
    intro i j heq
    exact Finset.singleton_injective (hi (by simpa only [Finset.sum_singleton] using heq))
  have hqn (i : Fin k) : q i ≠ 0 := by
    intro heq
    have hs : ({i} : Finset (Fin k))=∅ := hi (by simpa only [Finset.sum_singleton,Finset.sum_empty] using heq)
    have hc := congrArg Finset.card hs
    simp only [Finset.card_singleton,Finset.card_empty] at hc
    omega
  have hdinj : Function.Injective (fun i ↦ 2 • q i) := by
    intro i j heq
    apply hqi
    apply add_self_injective_zmod hd
    simpa only [two_nsmul] using heq
  have hclosed (i : Fin k) (hiB : i ∉ B) : ∃ j, q j=2 • q i := by
    have hiC : 2 • q i ∈ C := by simpa [B] using hiB
    obtain ⟨S,_,hS⟩ := Finset.mem_image.mp hiC
    rcases hrep i ⟨S,hS⟩ with hz | hj
    · have hzero : q i=0 := add_self_injective_zmod hd _ _ (by simpa only [two_nsmul,add_zero] using hz)
      exact False.elim (hqn i hzero)
    · exact hj
  let f : Fin k → Fin k := fun i ↦ if h : i ∉ B then Classical.choose (hclosed i h) else i
  have hf (i : Fin k) (hiB : i ∉ B) : q (f i)=2 • q i := by
    simpa only [f,dif_pos hiB] using Classical.choose_spec (hclosed i hiB)
  have hfinj : Set.InjOn f ((Bᶜ : Finset (Fin k)) : Set (Fin k)) := by
    intro i hiB j hjB heq
    apply hdinj
    change 2 • q i=2 • q j
    rw [← hf i (Finset.mem_compl.mp hiB),← hf j (Finset.mem_compl.mp hjB),heq]
  obtain ⟨P,hP⟩ := exists_perm_eq_on_finset_of_injOn Bᶜ f hfinj
  refine ⟨P,B,?_,fun i hiB ↦ by rw [hP i (Finset.mem_compl.mpr hiB)]; exact hf i hiB⟩
  have hsub : B.image (fun i ↦ 2 • q i) ⊆ Cᶜ := by
    intro z hz
    obtain ⟨i,hiB,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_compl.mpr (Finset.mem_filter.mp hiB).2
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hdinj] at hc
  have hcompl := Finset.card_compl_add_card C
  simp only [ZMod.card,hCcard] at hcompl
  omega

/-- General odd-index hole budget beside an ACTUAL cycle: each hole
can terminate at most floor(log2(2*m)) outside coordinates. This handles
arbitrary deficits, not only a finite list of near-tight capacities. -/
theorem outside_card_le_odd_index_holes_mul_log_of_valid_mapped_cycle
    {m k d : ℕ} (hm : 2 ≤ m) (hd : Odd d) [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) :
    k ≤ (d-2^k)*Nat.log 2 (2*m) := by
  classical
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero hd.pos.ne' (NeZero.ne _)⟩
  obtain ⟨β,hβ,hfactor⟩ := exists_bijective_scale_factor_of_injective_cyclic_hom τ hτ
  let u : Fin m → ZMod (2^m-1) := fun i ↦ β ((2^i.val : ℕ) : ZMod (2^m-1))
  have hcover (z : ZMod (2^m-1)) : ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z := by
    obtain ⟨w,hw⟩ := hβ.2 z
    obtain ⟨s,hs,hvalue⟩ := exists_power_multiset_sum_at_mersenne hm w
    refine ⟨s,hs,?_⟩
    rw [← hw,← hvalue,map_multiset_sum,Multiset.map_map]
    rfl
  have hp : ∀ i, g (Fin.castAdd k i)=zmodScaleHom d (2^m-1) (u i) := by
    intro i
    rw [hfactor]
    exact hpref i
  have hi := quotient_subset_sum_injective_of_actual_fibre_cover (by omega) g hg u hp hcover
  have hrep := quotient_double_eq_zero_or_entry_of_actual_fibre_cover (by omega) g hg u hp hcover
  obtain ⟨P,B,hB,hP⟩ := exists_partial_doubling_perm_with_card_le_cube_holes hd _ hi hrep
  exact (outside_card_le_exceptions_mul_log_of_valid_mapped_cycle hm τ hτ g hg hpref hi P B hP).trans
    (Nat.mul_le_mul_right _ hB)

/-- The arbitrary-hole bound for an actual affine cycle with a stated
odd subgroup index. Its ordering and injective subgroup map are extracted
from validity; the outside entries are unrestricted. -/
theorem outside_card_le_odd_index_holes_mul_log_of_valid_affine_cycle
    {m k d N : ℕ} [NeZero N] (hm : 2 ≤ m) (hd : Odd d) (hN : N=d*(2^m-1))
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hdouble : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    k ≤ (d-2^k)*Nat.log 2 (2*m) := by
  classical
  subst N
  have hpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  letI : NeZero (2^m-1) := ⟨hpos.ne'⟩
  let v : Fin (m+k) → ZMod (d*(2^m-1)) := fun i ↦ g (E i)+b
  have hv : ValidTuple v := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hvdouble : ∀ i, v (Fin.castAdd k (R i))=2 • v (Fin.castAdd k i) := by
    intro i
    dsimp [v]
    rw [hdouble]
    simp only [two_nsmul]
    abel
  let u : Fin m → ZMod (d*(2^m-1)) := fun i ↦ v (Fin.castAdd k i)
  have hu : ValidTuple u := validTuple_embedding ⟨Fin.castAdd k,Fin.castAdd_injective m k⟩ v hv
  obtain ⟨a,e,he⟩ := exists_doubling_orbit_equiv_of_valid_zmod (by omega) u hu R hvdouble
  have ho := addOrderOf_eq_mersenne_of_valid_doubling hm u hu R hvdouble a
  obtain ⟨τ,hτ,hτone⟩ := exists_cyclic_subgroup_hom_of_addOrderOf (u a) ho
  have hτnat (r : ℕ) : τ (r : ZMod (2^m-1))=r • u a := by
    have hr : (r : ZMod (2^m-1))=r • (1 : ZMod (2^m-1)) := by simp
    rw [hr,map_nsmul,hτone]
  let F : Equiv.Perm (Fin (m+k)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin k))).trans finSumFinEquiv)
  have hleft (i : Fin m) : F (Fin.castAdd k i)=Fin.castAdd k (e i) := by simp [F]
  apply outside_card_le_odd_index_holes_mul_log_of_valid_mapped_cycle hm hd τ hτ
    (fun i ↦ v (F i)) (validTuple_embedding F.toEmbedding v hv)
  intro i
  rw [hleft,hτnat]
  exact he i

/-- EVERY valid odd-modulus tuple with an actual affine doubling cycle
satisfies this structural quotient-hole budget. Neither a majority nor
a near-tight index nor a small number of exceptions is assumed. -/
theorem exists_odd_cycle_index_with_hole_budget
    {m k N : ℕ} (hm : 2 ≤ m) (hN : Odd N)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    ∃ d, Odd d ∧ N=d*(2^m-1) ∧ 2^k ≤ d ∧ k ≤ (d-2^k)*Nat.log 2 (2*m) := by
  letI : NeZero N := ⟨hN.pos.ne'⟩
  obtain ⟨hdiv,hcap⟩ := affine_doubling_cycle_fibre_capacity hm g hg E b R hd
  obtain ⟨d,hdN⟩ := hdiv
  have hfactor : N=d*(2^m-1) := by rw [hdN,Nat.mul_comm]
  have hdodd : Odd d := (Nat.odd_mul.mp (hfactor ▸ hN)).1
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hdlo : 2^k ≤ d := by rw [hfactor] at hcap; nlinarith
  exact ⟨d,hdodd,hfactor,hdlo,
    outside_card_le_odd_index_holes_mul_log_of_valid_affine_cycle hm hdodd hfactor g hg E b R hd⟩

/-- A purely arithmetic hole-budget test gives the STRONGER binary
lower bound for actual odd affine cycles, in arbitrary dimensions and
complement sizes. It consumes all possible subbinary odd indices at once;
2*((D+1)/2)-1 is the largest odd natural at most D. -/
theorem binary_lower_bound_of_valid_odd_affine_cycle_of_hole_budget
    {m k N : ℕ} (hm : 2 ≤ m) (hN : Odd N)
    (hbudget : (2*(((2^(m+k)-1)/(2^m-1)+1)/2)-1-2^k)*Nat.log 2 (2*m) < k)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    2^(m+k) ≤ N := by
  by_contra hnot
  obtain ⟨d,hdodd,hfactor,_,hholes⟩ := exists_odd_cycle_index_with_hole_budget hm hN g hg E b R hd
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hdhi : d ≤ (2^(m+k)-1)/(2^m-1) := by
    apply (Nat.le_div_iff_mul_le hRpos).mpr
    rw [← hfactor]
    omega
  have hdoddhi : d ≤ 2*(((2^(m+k)-1)/(2^m-1)+1)/2)-1 := by
    obtain ⟨r,hr⟩ := hdodd
    omega
  have hle := Nat.mul_le_mul_right (Nat.log 2 (2*m)) (Nat.sub_le_sub_right hdoddhi (2^k))
  omega

end MinModulus
