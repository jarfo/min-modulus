import MinModulus.CycleThinCover

/-!
# Tight actual-fibre capacity extracts a full outside quotient chain

Represent an outside double as a subset sum. Subset-sum injectivity
excludes the doubled coordinate from that subset; a full own-size
fibre cover excludes subsets of size at least two by an actual rival.
At exact cyclic capacity all doubles are representable, giving closure
up to zero. The actual half coordinate and almost-doubling geometry
then extract one complete chain under an actual permutation.

This applies to arbitrary full-cover fibres, not only SI or cycles.
It proves quotient relations, not actual upstairs equalities, and
does not assert that arbitrary critical fibres are full or tight.
-/

namespace MinModulus
open Finset

/-- In an injective subset cube, a subset representing a coordinate's
double cannot contain that coordinate. No tuple validity is assumed. -/
theorem not_mem_subset_of_sum_eq_double_of_subset_sum_injective
    {α G : Type*} [DecidableEq α] [AddCommGroup G] (q : α → G)
    (hi : Function.Injective (fun S : Finset α ↦ ∑ i ∈ S, q i))
    (j : α) (S : Finset α) (hS : (∑ i ∈ S, q i)=2 • q j) : j ∉ S := by
  intro hj
  have he : (∑ i ∈ S.erase j, q i)=q j := by
    have hs := Finset.sum_erase_add S q hj
    rw [hS,two_nsmul] at hs
    exact add_right_cancel hs
  have hsets : S.erase j={j} := hi (by simpa only [Finset.sum_singleton] using he)
  have hmem : j ∈ S.erase j := by rw [hsets]; exact Finset.mem_singleton_self j
  exact (Finset.mem_erase.mp hmem).1 rfl

/-- An actual full own-size fibre cover rules out representing an
outside double by two or more OTHER outside coordinates in the quotient.
The full cover absorbs the changed coin budget and omits a removed entry. -/
theorem not_validTuple_of_actual_fibre_cover_double_subset
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 0 < m)
    (g : Fin (m+k) → ZMod (d*M)) (u : Fin m → ZMod M)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=zmodScaleHom d M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)
    (i : Fin k) (S : Finset (Fin k)) (hiS : i ∉ S) (hScard : 2 ≤ S.card)
    (hrel : (∑ j ∈ S, ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m j)))=
      2 • ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i))) :
    ¬ ValidTuple g := by
  classical
  let τ := zmodScaleHom d M
  let π := ZMod.castHom (dvd_mul_right d M) (ZMod d)
  let f : Fin m → Fin (m+k) := Fin.castAdd k
  let e : Fin k → Fin (m+k) := Fin.natAdd m
  let i0 : Fin m := ⟨0,hm⟩
  let δ := S.card-2
  obtain ⟨j,hj⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hef (a : Fin m) (b : Fin k) : f a ≠ e b := by
    intro heq
    have he := congrArg Fin.val heq
    simp only [f,e,Fin.val_castAdd,Fin.val_natAdd] at he
    omega
  have heinj : Function.Injective e := by
    intro a b heq
    apply Fin.ext
    have he := congrArg Fin.val heq
    simp only [e,Fin.val_natAdd] at he
    omega
  have hker : π ((∑ j ∈ S, g (e j))-2 • g (e i))=0 := by
    rw [map_sub,map_sum,map_nsmul]
    change (∑ j ∈ S, π (g (e j)))-2 • π (g (e i))=0
    rw [hrel,sub_self]
  obtain ⟨w,hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hker
  let z : ZMod M := (∑ a, u a)+w-δ • u i0
  let t : Multiset (Fin (m+k)) := Multiset.replicate δ (f i0)+
    ((Finset.univ \ S).val.map e+Multiset.replicate 2 (e i))
  have hSle : S.card ≤ k := by simpa only [Fintype.card_fin] using Finset.card_le_univ S
  have htcard : m+t.card=m+k := by
    simp only [t,Multiset.card_add,Multiset.card_replicate,Multiset.card_map]
    change m+(δ+((Finset.univ \ S).card+2))=m+k
    simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin]
    dsimp [δ]
    omega
  have htotal : (∑ a, g a)=τ (∑ a, u a)+(∑ b : Fin k, g (e b)) := by
    rw [Fin.sum_univ_add]
    simp only [hpref,← map_sum,τ,e]
  have hsum : τ z+(t.map g).sum=∑ a, g a := by
    simp only [t,Multiset.map_add,Multiset.sum_add,Multiset.map_replicate,
      Multiset.sum_replicate,Multiset.map_map,Function.comp_def]
    change τ z+(δ • g (f i0)+((∑ b ∈ Finset.univ \ S, g (e b))+2 • g (e i)))=_
    rw [show g (f i0)=τ (u i0) from hpref i0]
    dsimp [z]
    rw [map_sub,map_add,map_nsmul,hw,htotal,← Finset.sum_sdiff (Finset.subset_univ S)]
    abel
  apply not_validTuple_of_actual_mapped_fibre_cover τ u g f hpref z (hcover z) t htcard hsum
    (e j) (fun a ↦ hef a j) ?_
  intro hmem
  rcases Multiset.mem_add.mp hmem with hrep | hrest
  · exact hef i0 j ((Multiset.mem_replicate.mp hrep).2.symm)
  · rcases Multiset.mem_add.mp hrest with hcomp | hrep
    · obtain ⟨a,ha,haj⟩ := Multiset.mem_map.mp hcomp
      have heq : a=j := heinj haj
      subst a
      exact (Finset.mem_sdiff.mp ha).2 hj
    · have hji : j=i := heinj (Multiset.mem_replicate.mp hrep).2
      exact hiS (hji ▸ hj)

/-- For any actual full-cover fibre, a representable outside quotient
double is zero or another actual quotient coordinate. -/
theorem quotient_double_eq_zero_or_entry_of_actual_fibre_cover
    {m k d M : ℕ} [NeZero M] [NeZero (d*M)] (hm : 0 < m)
    (g : Fin (m+k) → ZMod (d*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i, g (Fin.castAdd k i)=zmodScaleHom d M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)
    (i : Fin k)
    (hrep : ∃ S : Finset (Fin k),
      (∑ j ∈ S, ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m j)))=
        2 • ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i))) :
    2 • ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i))=0 ∨
      ∃ j, ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m j))=
        2 • ZMod.castHom (dvd_mul_right d M) (ZMod d) (g (Fin.natAdd m i)) := by
  classical
  obtain ⟨S,hS⟩ := hrep
  have hi := quotient_subset_sum_injective_of_actual_fibre_cover hm g hg u hpref hcover
  have hiS := not_mem_subset_of_sum_eq_double_of_subset_sum_injective _ hi i S hS
  have hsmall : S.card ≤ 1 := by
    by_contra hnot
    exact not_validTuple_of_actual_fibre_cover_double_subset hm g u hpref hcover i S hiS
      (by omega) hS hg
  by_cases hz : S.card=0
  · left
    rw [Finset.card_eq_zero.mp hz,Finset.sum_empty] at hS
    exact hS.symm
  · right
    obtain ⟨j,hj⟩ := Finset.card_eq_one.mp (by omega : S.card=1)
    exact ⟨j,by simpa only [hj,Finset.sum_singleton] using hS⟩

/-- Exact quotient capacity supplies every representation automatically:
outside quotient doubling is closed up to zero for ANY actual full-cover
fibre. No cycle, SI, or quotient-validity premise is used. -/
theorem quotient_doubling_closed_up_to_zero_of_tight_actual_fibre_cover
    {m k M : ℕ} [NeZero M] (hm : 0 < m)
    (g : Fin (m+k) → ZMod ((2^k)*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i, g (Fin.castAdd k i)=zmodScaleHom (2^k) M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z)
    (i : Fin k) :
    2 • ZMod.castHom (dvd_mul_right (2^k) M) (ZMod (2^k)) (g (Fin.natAdd m i))=0 ∨
      ∃ j, ZMod.castHom (dvd_mul_right (2^k) M) (ZMod (2^k)) (g (Fin.natAdd m j))=
        2 • ZMod.castHom (dvd_mul_right (2^k) M) (ZMod (2^k)) (g (Fin.natAdd m i)) := by
  letI : NeZero ((2^k)*M) := ⟨Nat.mul_ne_zero (by positivity) (NeZero.ne M)⟩
  have hi := quotient_subset_sum_injective_of_actual_fibre_cover hm g hg u hpref hcover
  have hsurj : Function.Surjective (fun S : Finset (Fin k) ↦
      ∑ j ∈ S, ZMod.castHom (dvd_mul_right (2^k) M) (ZMod (2^k)) (g (Fin.natAdd m j))) := by
    by_contra hnot
    have hlt := Fintype.card_lt_of_injective_not_surjective _ hi hnot
    simp only [Fintype.card_finset,Fintype.card_fin,ZMod.card] at hlt
    omega
  exact quotient_double_eq_zero_or_entry_of_actual_fibre_cover hm g hg u hpref hcover i (hsurj _)

/-- Subset-sum injectivity eliminates every nonempty doubling-permuted
remainder in an almost-doubling decomposition. The actual tuple is one
ordered chain, without any ValidTuple premise. -/
theorem exists_perm_chain_of_injective_subset_sums_almost_doubling
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (q : Fin n → G)
    (hi : Function.Injective (fun S : Finset (Fin n) ↦ ∑ i ∈ S, q i))
    (P : Equiv.Perm (Fin n)) (a : Fin n)
    (hd : ∀ i, i ≠ a → q (P i)=2 • q i) :
    ∃ E : Equiv.Perm (Fin n), ∃ x : G, ∀ i, q (E i)=2^i.val • x := by
  classical
  obtain ⟨m,k,hsize,_,E,R,x,hcycle,hchain⟩ :=
    exists_cycle_chain_of_almost_doubling_perm q P a hd
  let f : Fin m → Fin n := fun i ↦ E (Fin.castAdd k i)
  have hfi : Function.Injective f := E.injective.comp (Fin.castAdd_injective m k)
  have hzero : (∑ i : Fin m, q (f i))=0 :=
    sum_eq_zero_of_doubling_invariant R (fun i ↦ q (f i)) hcycle Finset.univ (by simp)
  have hsum : (∑ j ∈ Finset.univ.image f, q j)=0 := by
    rw [Finset.sum_image (fun _ _ _ _ h ↦ hfi h)]
    exact hzero
  have hempty : Finset.univ.image f=∅ := hi (by simpa only [Finset.sum_empty] using hsum)
  have hm0 : m=0 := by
    have hc := congrArg Finset.card hempty
    rw [Finset.card_image_of_injective _ hfi,Finset.card_univ,Fintype.card_fin,Finset.card_empty] at hc
    exact hc
  subst m
  simp only [zero_add] at hsize
  subst k
  let F : Fin n ≃ Fin (0+n) := (finCongr (Nat.zero_add n)).symm
  refine ⟨F.trans E,x,?_⟩
  intro i
  have hF : F i=Fin.natAdd 0 i := Fin.ext (by simp [F])
  change q (E (F i))=2^i.val • x
  rw [hF]
  exact hchain i

/-- A tight cyclic subset cube closed under doubling up to zero is
one ACTUAL full doubling chain, not merely a dyadic valuation pattern. -/
theorem exists_perm_chain_of_tight_subset_cube_doubling_closed
    {k D : ℕ} [NeZero D] (hcard : 2^k=2*D)
    (q : Fin k → ZMod (2*D))
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i))
    (hclosed : ∀ i, 2 • q i=0 ∨ ∃ j, q j=2 • q i) :
    ∃ E : Equiv.Perm (Fin k), ∃ x : ZMod (2*D), ∀ i, q (E i)=2^i.val • x := by
  classical
  have hD := Nat.pos_of_ne_zero (NeZero.ne D)
  letI : NeZero (2*D) := ⟨by omega⟩
  obtain ⟨a,ha⟩ := exists_half_coordinate_of_tight_subset_cube hcard q hi
  have hqi : Function.Injective q := by
    intro i j heq
    exact Finset.singleton_injective (hi (by simpa only [Finset.sum_singleton] using heq))
  have hqn (i : Fin k) : q i ≠ 0 := by
    intro heq
    have hs : ({i} : Finset (Fin k))=∅ := hi (by simpa only [Finset.sum_singleton,Finset.sum_empty] using heq)
    have hc := congrArg Finset.card hs
    simp only [Finset.card_singleton,Finset.card_empty] at hc
    omega
  have hinj : ∀ i, i ≠ a → ∀ j, j ≠ a → 2 • q i=2 • q j → i=j := by
    intro i _ j hja heq
    rcases eq_or_eq_add_half_of_castHom_eq (q i) (q j)
      (castHom_eq_of_two_nsmul_eq _ _ heq) with hij | hij
    · exact hqi hij
    · have hsum : (∑ b ∈ ({j,a} : Finset (Fin k)), q b)=q i := by
        rw [Finset.sum_pair hja,ha]
        exact hij.symm
      have hsets : ({j,a} : Finset (Fin k))={i} := hi (by simpa only [Finset.sum_singleton] using hsum)
      have hjmem : j ∈ ({i} : Finset (Fin k)) := hsets ▸ (by simp : j ∈ ({j,a} : Finset (Fin k)))
      have hamem : a ∈ ({i} : Finset (Fin k)) := hsets ▸ (by simp : a ∈ ({j,a} : Finset (Fin k)))
      have hji : j=i := Finset.mem_singleton.mp hjmem
      have hai : a=i := Finset.mem_singleton.mp hamem
      exact False.elim (hja (hji.trans hai.symm))
  have hcl : ∀ i, i ≠ a → ∃ j, q j=2 • q i+(0 : ZMod (2*D)) := by
    intro i hia
    rcases hclosed i with hz | hj
    · have hzero : 2 • q i=2 • (0 : ZMod (2*D)) := by simpa only [smul_zero] using hz
      rcases eq_or_eq_add_half_of_castHom_eq (q i) 0
        (castHom_eq_of_two_nsmul_eq _ _ hzero) with hi0 | hihalf
      · exact False.elim (hqn i hi0)
      · have hieq : q i=q a := by simpa only [zero_add,ha] using hihalf
        exact False.elim (hia (hqi hieq))
    · simpa only [add_zero] using hj
  obtain ⟨P,hP⟩ := exists_almost_doubling_perm_of_one_escape q a 0 hinj hcl
  exact exists_perm_chain_of_injective_subset_sums_almost_doubling q hi P a
    (by simpa only [add_zero] using hP)

/-- At tight capacity, the outside quotient of ANY actual full-cover
fibre is one complete doubling chain under an actual permutation.
No quotient validity, cycle fibre, SI structure, or size cutoff is assumed. -/
theorem exists_perm_quotient_chain_of_tight_actual_fibre_cover
    {m k M : ℕ} [NeZero M] (hm : 0 < m)
    (g : Fin (m+k) → ZMod ((2^k)*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i, g (Fin.castAdd k i)=zmodScaleHom (2^k) M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    ∃ E : Equiv.Perm (Fin k), ∃ x : ZMod (2^k), ∀ i,
      ZMod.castHom (dvd_mul_right (2^k) M) (ZMod (2^k)) (g (Fin.natAdd m (E i)))=2^i.val • x := by
  cases k with
  | zero => exact ⟨Equiv.refl _,0,fun i ↦ Fin.elim0 i⟩
  | succ k =>
    letI : NeZero ((2^(k+1))*M) := ⟨Nat.mul_ne_zero (by positivity) (NeZero.ne M)⟩
    have hi := quotient_subset_sum_injective_of_actual_fibre_cover hm g hg u hpref hcover
    have hcl := quotient_doubling_closed_up_to_zero_of_tight_actual_fibre_cover hm g hg u hpref hcover
    have h := exists_perm_chain_of_tight_subset_cube_doubling_closed (k := k+1) (D := 2^k)
    rw [← pow_succ'] at h
    exact h rfl _ hi hcl

end MinModulus
