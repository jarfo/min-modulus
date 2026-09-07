import MinModulus.TightFibreDoubling

/-!
# Tight-cycle rigidity and full majority-cycle bounds

Normalize arbitrary injective cyclic subgroup maps by an actual
bijective factor of canonical scaling. Tight full-cover capacity
extracts an outside quotient chain; thin Mersenne covers lift every
consecutive relation upstairs. The actual chain-size theorem therefore
forces the logarithmic cutoff without assuming it.

Below the binary threshold, the existing majority-cycle capacity
classification leaves only this tight case or the odd Mersenne
endpoint. Hence every majority affine doubling cycle satisfies the
full global and all exact-stratum bounds, with arbitrary outsiders.
Direct G3 exclusion is included. Arbitrary critical cycle extraction
and unrestricted G1/G2/G3 remain open.
-/

namespace MinModulus
open Finset

/-- A cyclic subgroup map factors through the canonical scaling map.
If the original map is injective, the factor is an actual automorphism. -/
theorem exists_bijective_scale_factor_of_injective_cyclic_hom
    {d M : ℕ} [NeZero M] [NeZero (d*M)]
    (τ : ZMod M →+ ZMod (d*M)) (hτ : Function.Injective τ) :
    ∃ β : ZMod M →+ ZMod M, Function.Bijective β ∧
      ∀ z, zmodScaleHom d M (β z)=τ z := by
  have hM := Nat.pos_of_ne_zero (NeZero.ne M)
  have hkill : M • τ 1=0 := by
    rw [← map_nsmul]
    have hz : M • (1 : ZMod M)=0 := by simp [nsmul_eq_mul]
    rw [hz,map_zero]
  have hdvd : d*M ∣ M*(τ 1).val := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    simpa only [Nat.cast_mul,ZMod.natCast_zmod_val,nsmul_eq_mul] using hkill
  have hd : d ∣ (τ 1).val := by
    have hdvd' : M*d ∣ M*(τ 1).val :=
      (show M*d ∣ d*M by rw [Nat.mul_comm]).trans hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hM hdvd'
  have hker : ZMod.castHom (dvd_mul_right d M) (ZMod d) (τ 1)=0 := by
    rw [ZMod.castHom_apply,← ZMod.natCast_val,ZMod.natCast_eq_zero_iff]
    exact hd
  obtain ⟨v,hv⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero _ hker
  let β : ZMod M →+ ZMod M :=
    { toFun := fun z ↦ z*v
      map_zero' := zero_mul v
      map_add' := fun a b ↦ add_mul a b v }
  have hfactor (z : ZMod M) : zmodScaleHom d M (β z)=τ z := by
    have hz : z=z.val • (1 : ZMod M) := by simp [nsmul_eq_mul]
    calc
      _=zmodScaleHom d M (z.val • v) := by
        congr 1
        change z*v=z.val • v
        simp [nsmul_eq_mul]
      _=z.val • τ 1 := by rw [map_nsmul,hv]
      _=τ z := by rw [← map_nsmul,← hz]
  have hβ : Function.Injective β := by
    intro a b hab
    apply hτ
    rw [← hfactor a,← hfactor b,hab]
  exact ⟨β,⟨hβ,Finite.injective_iff_surjective.mp hβ⟩,hfactor⟩

/-- Any quotient-kernel discrepancy has an ACTUAL preimage in every
injectively mapped subgroup of the full expected order. -/
theorem exists_cyclic_hom_preimage_of_castHom_eq_zero
    {d M : ℕ} [NeZero M] [NeZero (d*M)]
    (τ : ZMod M →+ ZMod (d*M)) (hτ : Function.Injective τ)
    (x : ZMod (d*M)) (hx : ZMod.castHom (dvd_mul_right d M) (ZMod d) x=0) :
    ∃ z, τ z=x := by
  obtain ⟨β,hβ,hfactor⟩ := exists_bijective_scale_factor_of_injective_cyclic_hom τ hτ
  obtain ⟨w,hw⟩ := exists_zmodScaleHom_eq_of_castHom_eq_zero x hx
  obtain ⟨z,hz⟩ := hβ.2 w
  exact ⟨z,by rw [← hfactor,hz,hw]⟩

/-- Tight quotient-chain extraction also applies to an arbitrarily
embedded full-order cyclic fibre, not just canonical scaling. -/
theorem exists_perm_quotient_chain_of_tight_mapped_fibre_cover
    {m k M : ℕ} [NeZero M] (hm : 0 < m)
    (τ : ZMod M →+ ZMod ((2^k)*M)) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod ((2^k)*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i, g (Fin.castAdd k i)=τ (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    ∃ E : Equiv.Perm (Fin k), ∃ x : ZMod (2^k), ∀ i,
      ZMod.castHom (dvd_mul_right (2^k) M) (ZMod (2^k)) (g (Fin.natAdd m (E i)))=2^i.val • x := by
  letI : NeZero ((2^k)*M) := ⟨Nat.mul_ne_zero (by positivity) (NeZero.ne M)⟩
  obtain ⟨β,hβ,hfactor⟩ := exists_bijective_scale_factor_of_injective_cyclic_hom τ hτ
  apply exists_perm_quotient_chain_of_tight_actual_fibre_cover hm g hg (fun i ↦ β (u i))
    (by intro i; rw [hfactor]; exact hpref i)
  intro z
  obtain ⟨w,hw⟩ := hβ.2 z
  obtain ⟨s,hs,hvalue⟩ := hcover w
  refine ⟨s,hs,?_⟩
  rw [← hw,← hvalue,map_multiset_sum,Multiset.map_map]
  rfl

/-- Any two distinct outsiders beside an actual mapped Mersenne cycle
inherit the exact-relation theorem by an actual subtuple embedding. -/
theorem outside_eq_double_of_valid_mapped_mersenne_cycle
    {m k : ℕ} (hm : 2 ≤ m) [NeZero (2^m-1)]
    {G : Type*} [AddCommGroup G] (τ : ZMod (2^m-1) →+ G)
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (a b : Fin k) (hab : a ≠ b)
    (hrel : ∃ z, τ z=2 • g (Fin.natAdd m a)-g (Fin.natAdd m b)) :
    g (Fin.natAdd m b)=2 • g (Fin.natAdd m a) := by
  classical
  let pair : Fin 2 → Fin k := ![a,b]
  have hpair : Function.Injective pair := by
    intro i j heq
    fin_cases i <;> fin_cases j <;> simp_all [pair]
  let join : Fin m ⊕ Fin 2 → Fin (m+k) :=
    Sum.elim (Fin.castAdd k) (fun j ↦ Fin.natAdd m (pair j))
  have hjoin : Function.Injective join := by
    rintro (i | i) (j | j) heq
    · exact congrArg Sum.inl (Fin.castAdd_injective m k heq)
    · have he := congrArg Fin.val heq
      change i.val=m+(pair j).val at he
      omega
    · have he := congrArg Fin.val heq
      change m+(pair i).val=j.val at he
      omega
    · apply congrArg Sum.inr
      apply hpair
      apply Fin.ext
      have he := congrArg Fin.val heq
      change m+(pair i).val=m+(pair j).val at he
      omega
  let f : Fin (m+2) ↪ Fin (m+k) :=
    finSumFinEquiv.symm.toEmbedding.trans ⟨join,hjoin⟩
  have hleft (i : Fin m) : f (Fin.castAdd 2 i)=Fin.castAdd k i := by simp [f,join]
  have hright (i : Fin 2) : f (Fin.natAdd m i)=Fin.natAdd m (pair i) := by simp [f,join]
  have h := extra_eq_double_of_valid_mapped_mersenne_cycle hm τ (fun i ↦ g (f i))
    (validTuple_embedding f g hg) (by intro i; rw [hleft,hpref])
    (by simpa [hright,pair] using hrel)
  simpa [hright,pair] using h

/-- Tight capacity forces the logarithmic outside-size cutoff beside
an ACTUAL mapped Mersenne cycle. First extract a quotient chain, then
lift every relation using thin covers, and apply zero-sum chain rigidity. -/
theorem two_pow_outside_le_length_of_valid_tight_mapped_cycle
    {m k : ℕ} (hm : 2 ≤ m) [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod ((2^k)*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod ((2^k)*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) :
    2^k ≤ m+k := by
  classical
  letI : NeZero ((2^k)*(2^m-1)) := ⟨Nat.mul_ne_zero (by positivity) (NeZero.ne _)⟩
  obtain ⟨E,x,hchain⟩ := exists_perm_quotient_chain_of_tight_mapped_fibre_cover
    (by omega) τ hτ g hg (fun i ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) hpref
    (exists_power_multiset_sum_at_mersenne hm)
  let π := ZMod.castHom (dvd_mul_right (2^k) (2^m-1)) (ZMod (2^k))
  have hstep (i j : Fin k) (hij : j.val=i.val+1) :
      g (Fin.natAdd m (E j))=2 • g (Fin.natAdd m (E i)) := by
    have hne : E i ≠ E j := by
      intro heq
      have hv := congrArg Fin.val (E.injective heq)
      omega
    apply outside_eq_double_of_valid_mapped_mersenne_cycle hm τ g hg hpref (E i) (E j) hne
    apply exists_cyclic_hom_preimage_of_castHom_eq_zero τ hτ
    rw [map_sub,map_nsmul]
    change 2 • π (g (Fin.natAdd m (E i)))-π (g (Fin.natAdd m (E j)))=0
    rw [hchain,hchain,hij,pow_succ',mul_smul,sub_self]
  by_cases hk : k=0
  · subst k
    norm_num
    omega
  · let a : Fin k := ⟨0,by omega⟩
    let y := g (Fin.natAdd m (E a))
    have hactual (r : ℕ) (hr : r < k) :
        g (Fin.natAdd m (E ⟨r,hr⟩))=2^r • y := by
      induction r with
      | zero => simp [y,a]
      | succ r ih =>
        rw [hstep ⟨r,by omega⟩ ⟨r+1,hr⟩ rfl,ih (by omega),pow_succ',mul_smul]
    let F : Equiv.Perm (Fin (m+k)) :=
      finSumFinEquiv.symm.trans ((Equiv.sumCongr (Equiv.refl (Fin m)) E).trans finSumFinEquiv)
    have hleft (i : Fin m) : F (Fin.castAdd k i)=Fin.castAdd k i := by simp [F]
    have hright (i : Fin k) : F (Fin.natAdd m i)=Fin.natAdd m (E i) := by simp [F]
    apply two_pow_chain_le_length_of_valid_zero_sum_fibre (by omega)
      (fun i ↦ g (F i)) (validTuple_embedding F.toEmbedding g hg) ?_ y ?_
    · simp only [hleft,hpref,← map_sum]
      rw [← Nat.cast_sum,sum_binary_powers,ZMod.natCast_self,map_zero]
    · intro i
      rw [hright]
      exact hactual i.val i.isLt

/-- An actual doubling-permuted cycle at its tight fibre capacity
forces the outside-size cutoff. The map and cycle ordering are extracted
from validity, not supplied as additional hypotheses. -/
theorem two_pow_outside_le_length_of_valid_tight_doubling_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hN : N=(2^k)*(2^m-1))
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i)) :
    2^k ≤ m+k := by
  classical
  subst N
  have hpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  letI : NeZero (2^m-1) := ⟨hpos.ne'⟩
  let u : Fin m → ZMod ((2^k)*(2^m-1)) := fun i ↦ g (Fin.castAdd k i)
  have hu : ValidTuple u := validTuple_embedding ⟨Fin.castAdd k,Fin.castAdd_injective m k⟩ g hg
  obtain ⟨a,e,he⟩ := exists_doubling_orbit_equiv_of_valid_zmod (by omega) u hu R hd
  have ho := addOrderOf_eq_mersenne_of_valid_doubling hm u hu R hd a
  obtain ⟨τ,hτ,hτone⟩ := exists_cyclic_subgroup_hom_of_addOrderOf (u a) ho
  have hτnat (r : ℕ) : τ (r : ZMod (2^m-1))=r • u a := by
    have hr : (r : ZMod (2^m-1))=r • (1 : ZMod (2^m-1)) := by simp
    rw [hr,map_nsmul,hτone]
  let F : Equiv.Perm (Fin (m+k)) :=
    finSumFinEquiv.symm.trans ((Equiv.sumCongr e (Equiv.refl (Fin k))).trans finSumFinEquiv)
  have hleft (i : Fin m) : F (Fin.castAdd k i)=Fin.castAdd k (e i) := by simp [F]
  apply two_pow_outside_le_length_of_valid_tight_mapped_cycle hm τ hτ
    (fun i ↦ g (F i)) (validTuple_embedding F.toEmbedding g hg)
  intro i
  rw [hleft,hτnat]
  exact he i

/-- FULL global lower bound for an actual affine doubling cycle
containing at least half the coordinates, with arbitrary outsiders.
The logarithmic outside cutoff is extracted in the only tight case
where it is needed; it is no longer an assumed restriction. -/
theorem global_lower_bound_of_valid_majority_affine_doubling_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hk : k ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    globalBound (m+k) ≤ N := by
  by_cases hsmall : N < 2^(m+k)
  · rcases modulus_eq_power_gap_or_mersenne_of_valid_majority_cycle hm hk hsmall g hg E b R hd
      with heq | heq
    · have hp : N=(2^k)*(2^m-1) := by
        rw [heq,pow_add,Nat.mul_sub_left_distrib,Nat.mul_one,Nat.mul_comm (2^k)]
      have hv : ValidTuple (fun i ↦ g (E i)+b) := by
        simpa only [sub_neg_eq_add] using
          validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
      have hpow := two_pow_outside_le_length_of_valid_tight_doubling_cycle hm hp _ hv R
        (by intro i; rw [hd]; simp only [two_nsmul]; abel)
      have hlog : k ≤ Nat.log 2 (m+k) := (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr hpow
      exact global_lower_bound_of_valid_large_affine_doubling_cycle hm hlog g hg E b R hd
    · rw [heq]
      exact Nat.sub_le_sub_left Nat.one_le_two_pow _
  · exact (Nat.sub_le _ _).trans (by omega)

/-- EVERY exact stratum for the entire majority-cycle class, with
no logarithmic outside-size premise and no restricted lift bits. -/
theorem stratum_lower_bound_of_valid_majority_affine_doubling_cycle
    {m k s q : ℕ} (hm : 2 ≤ m) (hk : k ≤ m) (hq : Odd q)
    (g : Fin (m+k) → ZMod (2^s*q)) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod (2^s*q)) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) s ≤ 2^s*q := by
  letI : NeZero (2^s*q) := ⟨Nat.mul_ne_zero (by positivity) hq.pos.ne'⟩
  by_cases hsmall : 2^s*q < 2^(m+k)
  · rcases modulus_eq_power_gap_or_mersenne_of_valid_majority_cycle hm hk hsmall g hg E b R hd
      with heq | heq
    · have hp : 2^s*q=(2^k)*(2^m-1) := by
        rw [heq,pow_add,Nat.mul_sub_left_distrib,Nat.mul_one,Nat.mul_comm (2^k)]
      have hv : ValidTuple (fun i ↦ g (E i)+b) := by
        simpa only [sub_neg_eq_add] using
          validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
      have hpow := two_pow_outside_le_length_of_valid_tight_doubling_cycle hm hp _ hv R
        (by intro i; rw [hd]; simp only [two_nsmul]; abel)
      have hlog : k ≤ Nat.log 2 (m+k) := (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr hpow
      exact stratum_lower_bound_of_valid_large_affine_doubling_cycle hm hlog hq g hg E b R hd
    · rw [heq]
      exact Nat.sub_le_sub_left Nat.one_le_two_pow _
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Direct G3 exclusion for EVERY majority affine doubling cycle,
not only cycles with logarithmically few outside entries. -/
theorem not_validTuple_exceptional_of_majority_affine_doubling_cycle
    {m k : ℕ} (hm : 2 ≤ m) (hk : k ≤ m)
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
  exact (not_lt_of_ge (global_lower_bound_of_valid_majority_affine_doubling_cycle hm hk g hg E b R hd)) hgap

end MinModulus
