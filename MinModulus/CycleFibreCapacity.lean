import MinModulus.ActualFibreQuotientCube
import MinModulus.G1DoublingCycleRigidity

/-!
# Actual doubling-cycle fibres reserve exponential outside capacity

A valid affine-doubling-permuted m-coordinate subtuple has exact subgroup
order 2^m-1 and a full m-coin cover there. Arbitrary k outside coordinates
therefore require 2^k distinct quotient subset sums, forcing
2^k*(2^m-1) <= N and (2^m-1) dividing N.

At odd N a cycle with m >= k gives the complete odd-stratum bound. At
any positive N a cycle with k <= floor(log2(m+k)) gives the full global
and every exact-stratum bound. The outside entries have no assumed SI,
doubling, parity, or lift-bit pattern. Affine translation and reindexing
are included. The cycle is ACTUAL input structure; extracting such a
cycle from an arbitrary critical tuple is not proved. G1/G2/G3 stay open.
-/

namespace MinModulus
open Finset

/-- A full own-size actual fibre has disjoint outside-subset translates.
This cardinal bound works for any finite abelian ambient group and any
injective cyclic subgroup map, not only the canonical divisor embedding. -/
theorem mul_two_pow_le_card_of_actual_mapped_fibre_cover
    {m k M : ℕ} [NeZero M] {G : Type*} [AddCommGroup G] [Fintype G]
    (hm : 0 < m) (τ : ZMod M →+ G) (hτ : Function.Injective τ)
    (g : Fin (m+k) → G) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i, g (Fin.castAdd k i)=τ (u i))
    (hcover : ∀ z, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    2^k*M ≤ Fintype.card G := by
  classical
  let f : Fin m → Fin (m+k) := Fin.castAdd k
  let e : Fin k → Fin (m+k) := Fin.natAdd m
  let i0 : Fin m := ⟨0,hm⟩
  have hef (i : Fin m) (j : Fin k) : f i ≠ e j := by
    intro h
    have hv := congrArg Fin.val h
    simp only [f,e,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  have heinj : Function.Injective e := by
    intro i j h
    apply Fin.ext
    have hv := congrArg Fin.val h
    simpa only [e,Fin.val_natAdd,Nat.add_left_cancel_iff] using hv
  have no_collision (S T : Finset (Fin k)) (hcard : S.card ≤ T.card) (hne : S ≠ T)
      (w : ZMod M) (hw : τ w=(∑ j ∈ T, g (e j))-(∑ j ∈ S, g (e j))) : False := by
    have hTcard : T.card ≤ k := by simpa only [Fintype.card_fin] using Finset.card_le_univ T
    have hnot : ¬ T ⊆ S := by
      intro hsub
      exact hne (Finset.eq_of_subset_of_card_le hsub hcard).symm
    obtain ⟨j,hjT,hjS⟩ := Finset.not_subset.mp hnot
    let δ := T.card-S.card
    let z := (∑ i, u i)+w-δ • u i0
    let t : Multiset (Fin (m+k)) := Multiset.replicate δ (f i0)+
      ((Finset.univ \ T).val.map e + S.val.map e)
    have htcard : m+t.card=m+k := by
      simp only [t,Multiset.card_add,Multiset.card_replicate,Multiset.card_map]
      change m+(δ+((Finset.univ \ T).card+S.card))=m+k
      simp only [Finset.card_sdiff,Finset.inter_univ,Finset.card_univ,Fintype.card_fin]
      dsimp [δ]
      omega
    have htotal : (∑ i, g i)=τ (∑ i, u i)+(∑ j : Fin k, g (e j)) := by
      rw [Fin.sum_univ_add]
      simp only [hpref,← map_sum,e]
    have hsum : τ z+(t.map g).sum=∑ i, g i := by
      simp only [t,Multiset.map_add,Multiset.sum_add,Multiset.map_replicate,
        Multiset.sum_replicate,Multiset.map_map,Function.comp_def]
      change τ z+(δ • g (f i0)+((∑ j ∈ Finset.univ \ T, g (e j))+(∑ j ∈ S, g (e j))))=_
      rw [show g (f i0)=τ (u i0) from hpref i0]
      dsimp [z]
      rw [map_sub,map_add,map_nsmul,hw,htotal,← Finset.sum_sdiff (Finset.subset_univ T)]
      abel
    apply not_validTuple_of_actual_mapped_fibre_cover τ u g f hpref z (hcover z) t htcard hsum
      (e j) (fun i ↦ hef i j) ?_ hg
    intro hmem
    rcases Multiset.mem_add.mp hmem with hrep | hrest
    · exact hef i0 j ((Multiset.mem_replicate.mp hrep).2.symm)
    · rcases Multiset.mem_add.mp hrest with hT | hS
      · obtain ⟨i,hi,hij⟩ := Multiset.mem_map.mp hT
        have heq : i=j := heinj hij
        subst i
        exact (Finset.mem_sdiff.mp hi).2 hjT
      · obtain ⟨i,hi,hij⟩ := Multiset.mem_map.mp hS
        have heq : i=j := heinj hij
        subst i
        exact hjS hi
  let value : Finset (Fin k) × ZMod M → G := fun p ↦ (∑ j ∈ p.1, g (e j))+τ p.2
  have hi : Function.Injective value := by
    rintro ⟨S,x⟩ ⟨T,y⟩ heq
    have hxy : τ (x-y)=(∑ j ∈ T, g (e j))-(∑ j ∈ S, g (e j)) := by
      change (∑ j ∈ S, g (e j))+τ x=(∑ j ∈ T, g (e j))+τ y at heq
      rw [map_sub]
      exact sub_eq_sub_iff_add_eq_add.mpr (by simpa only [add_comm] using heq)
    have hST : S=T := by
      by_contra hne
      rcases le_total S.card T.card with h | h
      · exact no_collision S T h hne (x-y) hxy
      · apply no_collision T S h (Ne.symm hne) (y-x)
        rw [← neg_sub x y,map_neg,hxy]
        abel
    subst T
    have hxy' : x=y := hτ (add_left_cancel heq)
    subst y
    rfl
  have hc := Fintype.card_le_of_injective value hi
  simpa only [Fintype.card_prod,Fintype.card_finset,Fintype.card_fin,ZMod.card] using hc

/-- Exactly m binary-orbit coins cover the whole Mersenne group. -/
theorem exists_power_multiset_sum_at_mersenne
    {m : ℕ} (hm : 2 ≤ m) [NeZero (2^m-1)] (z : ZMod (2^m-1)) :
    ∃ s : Multiset (Fin m), s.card=m ∧
      (s.map (fun i ↦ ((2^i.val : ℕ) : ZMod (2^m-1)))).sum=z := by
  have hp := Nat.lt_two_pow_self (n := m-1)
  have hpow : 2^m=2*2^(m-1) := by rw [← pow_succ']; congr 1; omega
  have hbound : 2^m-1 ≤ (1+2)*(2^(m-1)-1)-(m-2) := by omega
  obtain ⟨s,hs,hvalue⟩ := exists_fixed_multiset_sum_of_modulus_le_initial_interval
    (d := 1) hm hbound (z-(m : ZMod (2^m-1)))
  have hs' : s.card=m := by omega
  refine ⟨s,hs',?_⟩
  have ha (i : Fin m) : ((2^i.val : ℕ) : ZMod (2^m-1))=(a i.val : ZMod (2^m-1))+1 := by
    have hp : 0 < 2^i.val := by positivity
    have he : a i.val+1=2^i.val := by unfold a; omega
    simpa only [Nat.cast_add,Nat.cast_one] using
      (congrArg (fun x : ℕ ↦ (x : ZMod (2^m-1))) he).symm
  simp only [ha,Multiset.sum_map_add,Multiset.map_const',Multiset.sum_replicate,hs',
    nsmul_eq_mul,mul_one,hvalue,sub_add_cancel]

/-- Any element of exact order M gives an injective cyclic subgroup map. -/
theorem exists_cyclic_subgroup_hom_of_addOrderOf
    {M : ℕ} {G : Type*} [AddCommGroup G] (x : G) (hx : addOrderOf x=M) :
    ∃ τ : ZMod M →+ G, Function.Injective τ ∧ τ 1=x := by
  have hkill : (zmultiplesHom G x) (M : ℤ)=0 := by
    simp only [zmultiplesHom_apply,← hx,natCast_zsmul,addOrderOf_nsmul_eq_zero]
  let τ := ZMod.lift M ⟨zmultiplesHom G x,hkill⟩
  refine ⟨τ,?_,?_⟩
  · intro a b hab
    obtain ⟨a,rfl⟩ := ZMod.intCast_surjective a
    obtain ⟨b,rfl⟩ := ZMod.intCast_surjective b
    have hz : (a-b) • x=0 := by
      change ZMod.lift M ⟨zmultiplesHom G x,hkill⟩ (a : ZMod M)=
        ZMod.lift M ⟨zmultiplesHom G x,hkill⟩ (b : ZMod M) at hab
      simpa only [ZMod.lift_coe,zmultiplesHom_apply,sub_smul,sub_eq_zero] using hab
    have hd : (M : ℤ) ∣ a-b := by
      rw [← hx,addOrderOf_dvd_iff_zsmul_eq_zero]
      exact hz
    have hzmod : ((a-b : ℤ) : ZMod M)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (a-b) M).mpr hd
    simpa only [Int.cast_sub,sub_eq_zero] using hzmod
  · change ZMod.lift M ⟨zmultiplesHom G x,hkill⟩ (1 : ZMod M)=x
    simpa using ZMod.lift_coe M ⟨zmultiplesHom G x,hkill⟩ (1 : ℤ)

/-- An ACTUAL doubling-permuted m-coordinate subtuple forces the
Mersenne divisor and reserves a full factor 2^k for arbitrary outsiders. -/
theorem doubling_cycle_fibre_capacity
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i)) :
    (2^m-1) ∣ N ∧ 2^k*(2^m-1) ≤ N := by
  classical
  let x : Fin m → ZMod N := fun i ↦ g (Fin.castAdd k i)
  have hx : ValidTuple x := validTuple_embedding ⟨Fin.castAdd k,Fin.castAdd_injective m k⟩ g hg
  obtain ⟨a,e,he⟩ := exists_doubling_orbit_equiv_of_valid_zmod (by omega) x hx R hd
  have ho := addOrderOf_eq_mersenne_of_valid_doubling hm x hx R hd a
  have hpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  letI : NeZero (2^m-1) := ⟨hpos.ne'⟩
  obtain ⟨τ,hτ,hτone⟩ := exists_cyclic_subgroup_hom_of_addOrderOf (x a) ho
  have hτnat (r : ℕ) : τ (r : ZMod (2^m-1))=r • x a := by
    have hr : (r : ZMod (2^m-1))=r • (1 : ZMod (2^m-1)) := by simp
    rw [hr,map_nsmul,hτone]
  let u : Fin m → ZMod (2^m-1) := fun i ↦ ((2^(e.symm i).val : ℕ) : ZMod (2^m-1))
  have hpref : ∀ i, g (Fin.castAdd k i)=τ (u i) := by
    intro i
    rw [hτnat]
    exact (by simpa only [Equiv.apply_symm_apply,x] using he (e.symm i))
  have hcover (z : ZMod (2^m-1)) : ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z := by
    obtain ⟨s,hs,hvalue⟩ := exists_power_multiset_sum_at_mersenne hm z
    exact ⟨s.map e,by simpa only [Multiset.card_map] using hs,
      by simpa only [Multiset.map_map,Function.comp_def,u,Equiv.symm_apply_apply] using hvalue⟩
  refine ⟨?_,?_⟩
  · rw [← ho]
    simpa using (addOrderOf_dvd_card (x := x a))
  · simpa only [ZMod.card] using
      mul_two_pow_le_card_of_actual_mapped_fibre_cover (by omega) τ hτ g hg u hpref hcover

/-- Reindexing and affine translation are permitted for the ACTUAL
cycle. Outside coordinates have no shape or parity restriction. -/
theorem affine_doubling_cycle_fibre_capacity
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    (2^m-1) ∣ N ∧ 2^k*(2^m-1) ≤ N := by
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  apply doubling_cycle_fibre_capacity hm _ hv R
  intro i
  rw [hd]
  simp only [two_nsmul]
  abel

/-- A cycle with at most floor(log2 n) arbitrary outsiders already
forces the FULL global lower bound, in every modulus and dimension. -/
theorem global_lower_bound_of_valid_large_affine_doubling_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hk : k ≤ Nat.log 2 (m+k))
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    globalBound (m+k) ≤ N := by
  have hcap := (affine_doubling_cycle_fibre_capacity hm g hg E b R hd).2
  have hp : 0 < 2^m := by positivity
  have hprod : 2^k*(2^m-1)+2^k=2^(m+k) := by
    calc
      _=2^k*((2^m-1)+1) := by ring
      _=2^k*2^m := by rw [Nat.sub_add_cancel hp]
      _=2^(m+k) := by rw [pow_add]; ring
  have hpow : 2^k ≤ 2^Nat.log 2 (m+k) := Nat.pow_le_pow_right (by omega) hk
  unfold globalBound
  omega

/-- At odd modulus a cycle containing at least HALF the coordinates
forces the FULL odd-stratum threshold. Arbitrarily many outsiders are
allowed; none is assumed to lie on a chain or a coherent prefix. -/
theorem odd_lower_bound_of_valid_majority_affine_doubling_cycle
    {m k N : ℕ} (hm : 2 ≤ m) (hk : k ≤ m) (hN : Odd N)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    2^(m+k)-1 ≤ N := by
  letI : NeZero N := ⟨hN.pos.ne'⟩
  obtain ⟨hdiv,hcap⟩ := affine_doubling_cycle_fibre_capacity hm g hg E b R hd
  by_cases hk0 : k=0
  · subst k
    simpa using hcap
  obtain ⟨d,hdN⟩ := hdiv
  have hdOdd : Odd d := Nat.Odd.of_mul_right (hdN ▸ hN)
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hdle : 2^k ≤ d := by rw [hdN] at hcap; nlinarith
  have hdne : d ≠ 2^k := by
    intro heq
    have htwo : 2 ∣ 2^k := by
      simpa only [pow_one] using pow_dvd_pow 2 (by omega : 1 ≤ k)
    exact hdOdd.not_two_dvd_nat (heq ▸ htwo)
  have hpow : 2^k ≤ 2^m := Nat.pow_le_pow_right (by omega) hk
  have hdle' : 2^k+1 ≤ d := by omega
  have hbound : (2^k+1)*(2^m-1) ≤ N := by
    rw [hdN,Nat.mul_comm (2^m-1) d]
    exact Nat.mul_le_mul_right _ hdle'
  have hRsum : (2^m-1)+1=2^m := Nat.sub_add_cancel (by
    have := Nat.one_lt_two_pow (show m ≠ 0 by omega)
    omega)
  have hprod : 2^k*(2^m-1)+2^k=2^m*2^k := by
    calc
      _=2^k*((2^m-1)+1) := by ring
      _=2^k*2^m := by rw [hRsum]
      _=2^m*2^k := by ring
  rw [add_mul,one_mul] at hbound
  rw [pow_add]
  omega

/-- Below the binary threshold, a majority cycle forces one of just
two actual moduli: its outside-dimension power gap or the odd endpoint. -/
theorem modulus_eq_power_gap_or_mersenne_of_valid_majority_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hk : k ≤ m) (hN : N < 2^(m+k))
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    N=2^(m+k)-2^k ∨ N=2^(m+k)-1 := by
  obtain ⟨hdiv,hcap⟩ := affine_doubling_cycle_fibre_capacity hm g hg E b R hd
  obtain ⟨d,hdN⟩ := hdiv
  have hRpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  have hRsum : (2^m-1)+1=2^m := Nat.sub_add_cancel (by omega)
  have hdle : 2^k ≤ d := by rw [hdN] at hcap; nlinarith
  have hprod : 2^k*(2^m-1)+2^k=2^(m+k) := by
    calc
      _=2^k*((2^m-1)+1) := by ring
      _=2^k*2^m := by rw [hRsum]
      _=2^(m+k) := by rw [pow_add]; ring
  by_cases heq : d=2^k
  · left
    rw [heq,Nat.mul_comm] at hdN
    omega
  · right
    have hdle' : 2^k+1 ≤ d := by omega
    have hbound : (2^k+1)*(2^m-1) ≤ N := by
      rw [hdN,Nat.mul_comm (2^m-1) d]
      exact Nat.mul_le_mul_right _ hdle'
    have hpow : 2^k ≤ 2^m := Nat.pow_le_pow_right (by omega) hk
    rw [add_mul,one_mul] at hbound
    omega

/-- The same logarithmic-outside class satisfies EVERY exact stratum,
not just the global envelope. No separate propagation case is left open. -/
theorem stratum_lower_bound_of_valid_large_affine_doubling_cycle
    {m k s q : ℕ} (hm : 2 ≤ m) (hk : k ≤ Nat.log 2 (m+k)) (hq : Odd q)
    (g : Fin (m+k) → ZMod (2^s*q)) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod (2^s*q)) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) s ≤ 2^s*q := by
  have hpos : 0 < 2^s*q := mul_pos (by positivity) hq.pos
  letI : NeZero (2^s*q) := ⟨hpos.ne'⟩
  by_cases hsmall : 2^s*q < 2^(m+k)
  · have hkm : k ≤ m := by
      have hpow : 2^k ≤ m+k := (Nat.pow_le_pow_right (by omega) hk).trans
        (Nat.pow_log_le_self 2 (by omega))
      have hlinear := two_mul_le_two_pow k
      omega
    rcases modulus_eq_power_gap_or_mersenne_of_valid_majority_cycle hm hkm hsmall g hg E b R hd
      with heq | heq
    · have htwodvd : 2^k ∣ 2^s*q := by
        rw [heq]
        exact Nat.dvd_sub (pow_dvd_pow 2 (by omega : k ≤ m+k)) (dvd_refl _)
      have hks : k ≤ s := by
        by_contra hnot
        have hstep : 2^s*2 ∣ 2^s*q := by
          rw [← pow_succ]
          exact (pow_dvd_pow 2 (by omega : s+1 ≤ k)).trans htwodvd
        exact hq.not_two_dvd_nat (Nat.dvd_of_mul_dvd_mul_left (by positivity) hstep)
      rw [heq]
      exact Nat.sub_le_sub_left (Nat.pow_le_pow_right (by omega) (le_min hks hk)) _
    · rw [heq]
      exact Nat.sub_le_sub_left (by
        have hp : 0 < 2^(min s (Nat.log 2 (m+k))) := by positivity
        omega) _
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Direct G3 consumer for the logarithmic-outside cycle class.
The unrestricted exceptional-lift statement remains unproved. -/
theorem not_validTuple_exceptional_of_large_affine_doubling_cycle
    {m k : ℕ} (hm : 2 ≤ m) (hk : k ≤ Nat.log 2 (m+k))
    (hnpow : 2^Nat.log 2 (m+k) ≠ m+k)
    (g : Fin (m+k) → ZMod (2*globalBound (m+k-1)))
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod (2*globalBound (m+k-1)))
    (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    ¬ ValidTuple g := by
  intro hg
  have hn3 : 3 ≤ m+k := by
    by_contra hnot
    have hn2 : m+k=2 := by omega
    norm_num [hn2] at hnpow
  have hB : 2 ≤ globalBound (m+k-1) := (nmin_eq (by omega : 2 ≤ m+k-1)).1.1
  letI : NeZero (2*globalBound (m+k-1)) := ⟨by omega⟩
  have hnpow' : 2^Nat.log 2 ((m+k-1)+1) ≠ (m+k-1)+1 := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m+k)] using hnpow
  have hgap : 2*globalBound (m+k-1) < globalBound (m+k) := by
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ m+k)] using
      two_mul_globalBound_lt_succ_of_not_power (by omega) hnpow'
  exact (not_lt_of_ge (global_lower_bound_of_valid_large_affine_doubling_cycle hm hk g hg E b R hd)) hgap

end MinModulus
