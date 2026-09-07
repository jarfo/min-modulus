import MinModulus.CycleTightRigidity

/-!
# One quotient hole and the complete half-sized-cycle class

At index 2^k+1, a full-cover fibre's outside cube misses one value.
Odd doubling is injective, so at most one coordinate can escape the
represented doubles; actual full-cover rivals force every represented
double to be an entry. The almost-doubling geometry extracts a full
quotient chain without a cycle or SI assumption on the fibre.

For actual Mersenne cycles, thin covers lift the chain and force its
size cutoff. When k=m+1, subbinary capacity leaves three possible
indices; tight and one-hole indices are excluded, leaving 2^n-2.
Together with majority-cycle bounds this closes global, all exact
strata, and G3 for cycles of at least floor(n/2) coordinates.
Arbitrary critical structure and unrestricted G1/G2/G3 remain open.
-/

namespace MinModulus
open Finset

/-- In an odd cyclic group with one missing cube value, every doubled
coordinate except at most one is represented. If represented doubles
are zero or actual entries, the cube is an actual full doubling chain. -/
theorem exists_perm_chain_of_one_hole_subset_cube
    {k d : ℕ} (hk : 0 < k) (hd : Odd d) (hcard : d=2^k+1)
    (q : Fin k → ZMod d)
    (hi : Function.Injective (fun S : Finset (Fin k) ↦ ∑ i ∈ S, q i))
    (hrep : ∀ i, (∃ S : Finset (Fin k), (∑ j ∈ S, q j)=2 • q i) →
      2 • q i=0 ∨ ∃ j, q j=2 • q i) :
    ∃ E : Equiv.Perm (Fin k), ∃ x : ZMod d, ∀ i, q (E i)=2^i.val • x := by
  classical
  letI : NeZero d := ⟨hd.pos.ne'⟩
  let C : Finset (ZMod d) := Finset.univ.image (fun S : Finset (Fin k) ↦ ∑ j ∈ S, q j)
  have hCcard : C.card=2^k := by
    simp only [C,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_finset,Fintype.card_fin]
  have hcompcard : Cᶜ.card=1 := by
    have hc := Finset.card_compl_add_card C
    simp only [ZMod.card,hcard,hCcard] at hc
    omega
  obtain ⟨w,hw⟩ := Finset.card_eq_one.mp hcompcard
  have hmissing (z : ZMod d) (hz : z ∉ C) : z=w := by
    have hc : z ∈ Cᶜ := Finset.mem_compl.mpr hz
    rw [hw] at hc
    exact Finset.mem_singleton.mp hc
  have hqi : Function.Injective q := by
    intro i j heq
    exact Finset.singleton_injective (hi (by simpa only [Finset.sum_singleton] using heq))
  have hqn (i : Fin k) : q i ≠ 0 := by
    intro heq
    have hs : ({i} : Finset (Fin k))=∅ := hi (by simpa only [Finset.sum_singleton,Finset.sum_empty] using heq)
    have hc := congrArg Finset.card hs
    simp only [Finset.card_singleton,Finset.card_empty] at hc
    omega
  have hdoubleinj : Function.Injective (fun i ↦ 2 • q i) := by
    intro i j heq
    apply hqi
    apply add_self_injective_zmod hd
    simpa only [two_nsmul] using heq
  have hentry (i : Fin k) (hiC : 2 • q i ∈ C) : ∃ j, q j=2 • q i := by
    obtain ⟨S,_,hS⟩ := Finset.mem_image.mp hiC
    rcases hrep i ⟨S,hS⟩ with hz | hj
    · have hzero : q i=0 := add_self_injective_zmod hd _ _ (by simpa only [two_nsmul,add_zero] using hz)
      exact False.elim (hqn i hzero)
    · exact hj
  have hone : ∃ a : Fin k, ∀ i, i ≠ a → ∃ j, q j=2 • q i := by
    by_cases hbad : ∃ a : Fin k, 2 • q a ∉ C
    · obtain ⟨a,ha⟩ := hbad
      refine ⟨a,?_⟩
      intro i hia
      apply hentry
      by_contra hiC
      exact hia (hdoubleinj ((hmissing _ hiC).trans (hmissing _ ha).symm))
    · refine ⟨⟨0,hk⟩,fun i _ ↦ hentry i ?_⟩
      by_contra hiC
      exact hbad ⟨i,hiC⟩
  obtain ⟨a,ha⟩ := hone
  obtain ⟨P,hP⟩ := exists_almost_doubling_perm_of_one_escape q a 0
    (fun i _ j _ hij ↦ hdoubleinj hij) (by simpa only [add_zero] using ha)
  exact exists_perm_chain_of_injective_subset_sums_almost_doubling q hi P a
    (by simpa only [add_zero] using hP)

/-- An arbitrary actual full-cover fibre at index 2^k+1 also forces
one entire outside quotient chain. The single cube hole permits only
one escape, which is enough to extract the full geometry. -/
theorem exists_perm_quotient_chain_of_one_hole_actual_fibre_cover
    {m k M : ℕ} [NeZero M] (hm : 0 < m)
    (g : Fin (m+k) → ZMod ((2^k+1)*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i, g (Fin.castAdd k i)=zmodScaleHom (2^k+1) M (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    ∃ E : Equiv.Perm (Fin k), ∃ x : ZMod (2^k+1), ∀ i,
      ZMod.castHom (dvd_mul_right (2^k+1) M) (ZMod (2^k+1)) (g (Fin.natAdd m (E i)))=2^i.val • x := by
  cases k with
  | zero => exact ⟨Equiv.refl _,0,fun i ↦ Fin.elim0 i⟩
  | succ k =>
    letI : NeZero ((2^(k+1)+1)*M) := ⟨Nat.mul_ne_zero (by positivity) (NeZero.ne M)⟩
    have hd : Odd (2^(k+1)+1) := by rw [pow_succ']; exact ⟨2^k,rfl⟩
    exact exists_perm_chain_of_one_hole_subset_cube (by omega) hd rfl _
      (quotient_subset_sum_injective_of_actual_fibre_cover hm g hg u hpref hcover)
      (quotient_double_eq_zero_or_entry_of_actual_fibre_cover hm g hg u hpref hcover)

/-- The one-hole chain theorem transports through arbitrary injective
cyclic subgroup maps, with no ambient-unit assumption. -/
theorem exists_perm_quotient_chain_of_one_hole_mapped_fibre_cover
    {m k M : ℕ} [NeZero M] (hm : 0 < m)
    (τ : ZMod M →+ ZMod ((2^k+1)*M)) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod ((2^k+1)*M)) (hg : ValidTuple g) (u : Fin m → ZMod M)
    (hpref : ∀ i, g (Fin.castAdd k i)=τ (u i))
    (hcover : ∀ z : ZMod M, ∃ s : Multiset (Fin m), s.card=m ∧ (s.map u).sum=z) :
    ∃ E : Equiv.Perm (Fin k), ∃ x : ZMod (2^k+1), ∀ i,
      ZMod.castHom (dvd_mul_right (2^k+1) M) (ZMod (2^k+1)) (g (Fin.natAdd m (E i)))=2^i.val • x := by
  letI : NeZero ((2^k+1)*M) := ⟨Nat.mul_ne_zero (by positivity) (NeZero.ne M)⟩
  obtain ⟨β,hβ,hfactor⟩ := exists_bijective_scale_factor_of_injective_cyclic_hom τ hτ
  apply exists_perm_quotient_chain_of_one_hole_actual_fibre_cover hm g hg (fun i ↦ β (u i))
    (by intro i; rw [hfactor]; exact hpref i)
  intro z
  obtain ⟨w,hw⟩ := hβ.2 z
  obtain ⟨s,hs,hvalue⟩ := hcover w
  refine ⟨s,hs,?_⟩
  rw [← hw,← hvalue,map_multiset_sum,Multiset.map_map]
  rfl

/-- At ANY subgroup index, a quotient chain beside a full-order
mapped Mersenne cycle lifts upstairs and forces the actual size cutoff. -/
theorem two_pow_outside_le_length_of_valid_mapped_cycle_quotient_chain
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero (2^m-1)] [NeZero (d*(2^m-1))]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (E : Equiv.Perm (Fin k)) (x : ZMod d)
    (hchain : ∀ i, ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d)
      (g (Fin.natAdd m (E i)))=2^i.val • x) : 2^k ≤ m+k := by
  classical
  let π := ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d)
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

/-- A mapped cycle at one-hole capacity forces the outside-size cutoff
in every dimension, without assuming an outside chain or majority. -/
theorem two_pow_outside_le_length_of_valid_one_hole_mapped_cycle
    {m k : ℕ} (hm : 2 ≤ m) [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod ((2^k+1)*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod ((2^k+1)*(2^m-1))) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) :
    2^k ≤ m+k := by
  letI : NeZero ((2^k+1)*(2^m-1)) := ⟨Nat.mul_ne_zero (by positivity) (NeZero.ne _)⟩
  obtain ⟨E,x,hchain⟩ := exists_perm_quotient_chain_of_one_hole_mapped_fibre_cover
    (by omega) τ hτ g hg (fun i ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) hpref
    (exists_power_multiset_sum_at_mersenne hm)
  exact two_pow_outside_le_length_of_valid_mapped_cycle_quotient_chain hm τ hτ g hg hpref E x hchain

/-- The actual cycle ordering and subgroup map at one-hole capacity
are extracted from validity, not added as new hypotheses. -/
theorem two_pow_outside_le_length_of_valid_one_hole_doubling_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hN : N=(2^k+1)*(2^m-1))
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (Fin.castAdd k (R i))=2 • g (Fin.castAdd k i)) :
    2^k ≤ m+k := by
  classical
  subst N
  have hpos : 0 < 2^m-1 := Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by omega))
  letI : NeZero (2^m-1) := ⟨hpos.ne'⟩
  let u : Fin m → ZMod ((2^k+1)*(2^m-1)) := fun i ↦ g (Fin.castAdd k i)
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
  apply two_pow_outside_le_length_of_valid_one_hole_mapped_cycle hm τ hτ
    (fun i ↦ g (F i)) (validTuple_embedding F.toEmbedding g hg)
  intro i
  rw [hleft,hτnat]
  exact he i

/-- If the cycle has exactly one fewer coordinate than its complement,
subbinary validity forces the first-even endpoint. Capacity leaves only
zero, one, or two quotient holes; the first two have a forbidden long chain. -/
theorem modulus_eq_binary_sub_two_of_valid_almost_half_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hk : k=m+1) (hN : N < 2^(m+k))
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    N=2^(m+k)-2 := by
  obtain ⟨hdiv,hcap⟩ := affine_doubling_cycle_fibre_capacity hm g hg E b R hd
  obtain ⟨d,hdN⟩ := hdiv
  have hQ : 4 ≤ 2^m := by simpa only [show (2 : ℕ)^2=4 by decide] using Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hm
  have hR : (2^m-1)+1=2^m := Nat.sub_add_cancel (by omega)
  have hA : 2^k=2*2^m := by rw [hk,pow_succ']
  have hP : 2^(m+k)=2^m*2^k := pow_add _ _ _
  have hdlo : 2^k ≤ d := by rw [hdN] at hcap; nlinarith
  have hdhi : d ≤ 2^k+2 := by
    by_contra hnot
    have hle := Nat.mul_le_mul_left (2^m-1) (by omega : 2^k+3 ≤ d)
    rw [← hdN] at hle
    nlinarith
  have hlong : m+k < 2^k := by
    have hl := two_mul_le_two_pow m
    omega
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hdouble : ∀ i, g (E (Fin.castAdd k (R i)))+b=2 • (g (E (Fin.castAdd k i))+b) := by
    intro i
    rw [hd]
    simp only [two_nsmul]
    abel
  have hcases : d=2^k ∨ d=2^k+1 ∨ d=2^k+2 := by omega
  rcases hcases with hdz | hdo | hdt
  · have hscale : N=(2^k)*(2^m-1) := by rw [hdN,hdz,Nat.mul_comm]
    exact False.elim ((not_lt_of_ge (two_pow_outside_le_length_of_valid_tight_doubling_cycle hm hscale _ hv R hdouble)) hlong)
  · have hscale : N=(2^k+1)*(2^m-1) := by rw [hdN,hdo,Nat.mul_comm]
    exact False.elim ((not_lt_of_ge (two_pow_outside_le_length_of_valid_one_hole_doubling_cycle hm hscale _ hv R hdouble)) hlong)
  · have hprod : (2^m-1)*(2^k+2)+2=2^(m+k) := by nlinarith
    rw [hdN,hdt]
    omega

/-- FULL global bound when an actual affine cycle has at least
floor(n/2) coordinates, including the odd-length almost-half case. -/
theorem global_lower_bound_of_valid_half_sized_affine_doubling_cycle
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m) (hk : k ≤ m+1)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    globalBound (m+k) ≤ N := by
  by_cases hkm : k ≤ m
  · exact global_lower_bound_of_valid_majority_affine_doubling_cycle hm hkm g hg E b R hd
  by_cases hsmall : N < 2^(m+k)
  · have heq := modulus_eq_binary_sub_two_of_valid_almost_half_cycle hm (by omega) hsmall g hg E b R hd
    have hv : Valid (m+k) N := by
      rw [heq]
      exact valid_gap (t := 1) (by omega) (by norm_num; omega)
    have hNge : 2 ≤ N := by
      have hc := Fintype.card_le_of_injective _ (validTuple_injective g hg)
      simp only [Fintype.card_fin,ZMod.card] at hc
      omega
    exact (nmin_eq (by omega : 2 ≤ m+k)).2 ⟨hNge,hv⟩
  · exact (Nat.sub_le _ _).trans (by omega)

/-- EVERY exact stratum for the entire half-sized affine cycle class;
the additional odd-length case has same-modulus fixed validity below binary. -/
theorem stratum_lower_bound_of_valid_half_sized_affine_doubling_cycle
    {m k s q : ℕ} (hm : 2 ≤ m) (hk : k ≤ m+1) (hq : Odd q)
    (g : Fin (m+k) → ZMod (2^s*q)) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b : ZMod (2^s*q)) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b) :
    stratumBound (m+k) s ≤ 2^s*q := by
  by_cases hkm : k ≤ m
  · exact stratum_lower_bound_of_valid_majority_affine_doubling_cycle hm hkm hq g hg E b R hd
  letI : NeZero (2^s*q) := ⟨Nat.mul_ne_zero (by positivity) hq.pos.ne'⟩
  by_cases hsmall : 2^s*q < 2^(m+k)
  · have heq := modulus_eq_binary_sub_two_of_valid_almost_half_cycle hm (by omega) hsmall g hg E b R hd
    apply stratum_lower_bound_of_valid_fixed (by omega) hq
    rw [heq]
    exact valid_gap (t := 1) (by omega) (by norm_num; omega)
  · exact (Nat.sub_le _ _).trans (by omega)

/-- Direct exceptional G3 exclusion for the entire half-sized cycle
class. No index, lift-bit, or logarithmic outside restriction is added. -/
theorem not_validTuple_exceptional_of_half_sized_affine_doubling_cycle
    {m k : ℕ} (hm : 2 ≤ m) (hk : k ≤ m+1)
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
  exact (not_lt_of_ge (global_lower_bound_of_valid_half_sized_affine_doubling_cycle hm hk g hg E b R hd)) hgap

end MinModulus
