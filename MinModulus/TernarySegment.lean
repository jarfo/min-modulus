import MinModulus.TriplingOrder
import MinModulus.G1OddPrimarySingletonComplement


/-!
# Modulus bounds for initial ternary orbit segments

Finite ternary splitting preserves the represented value and increases the
number of coins by two. A balanced ternary representation of twice an
annihilator therefore gives a rival whenever the ternary total is at least
that displacement plus the tuple length. Consequently a valid affine
ternary segment modulo positive N satisfies 3^n+1 ≤ 4*N+2*n. For odd N,
parity strengthens this to the G2 bound 2^n-1 ≤ N. No last-to-first closure,
inductive conjecture, or finite cutoff is assumed.
-/

namespace MinModulus
open Finset

/-- Ternary splitting reaches every cardinality of the same parity
between the initial number of coins and the total unit-coin weight. -/
theorem exists_ranked_ternary_refinement
    {α A : Type*} [AddCommMonoid A] (rank : α → ℕ) (x : α → A)
    (hpred : ∀ i, 0 < rank i → ∃ j, rank i=rank j+1 ∧ x i=3 • x j)
    (s : Multiset α) (r : ℕ)
    (hupper : s.card+2*r ≤ (s.map (fun i ↦ (3:ℕ)^(rank i))).sum) :
    ∃ t : Multiset α, t.card=s.card+2*r ∧ (t.map x).sum=(s.map x).sum := by
  classical
  induction r generalizing s with
  | zero => exact ⟨s,by omega,rfl⟩
  | succ r ih =>
    have hex : ∃ i ∈ s, 0 < rank i := by
      by_contra hn
      push Not at hn
      have hmap : s.map (fun i ↦ (3:ℕ)^(rank i))=s.map (fun _ ↦ (1:ℕ)) := by
        apply Multiset.map_congr rfl
        intro i hi
        rw [show rank i=0 by have := hn i hi; omega,pow_zero]
      have hunit : (s.map (fun i ↦ (3:ℕ)^(rank i))).sum = s.card := by
        rw [hmap]
        simp
      rw [hunit] at hupper
      omega
    obtain ⟨i,hi,hrank⟩ := hex
    obtain ⟨j,hj,hx⟩ := hpred i hrank
    have hs : i ::ₘ s.erase i=s := Multiset.cons_erase hi
    let p := j ::ₘ j ::ₘ j ::ₘ s.erase i
    have hp : p.card=s.card+2 := by
      have h := congrArg Multiset.card hs
      simp only [Multiset.card_cons] at h
      simp only [p,Multiset.card_cons]
      omega
    have hpval : (p.map (fun i ↦ (3:ℕ)^(rank i))).sum=(s.map (fun i ↦ (3:ℕ)^(rank i))).sum := by
      conv_rhs => rw [← hs]
      simp only [p,Multiset.map_cons,Multiset.sum_cons,hj,pow_succ]
      omega
    have hpx : (p.map x).sum=(s.map x).sum := by
      conv_rhs => rw [← hs]
      simp only [p,Multiset.map_cons,Multiset.sum_cons,hx,three_nsmul,add_assoc]
    obtain ⟨t,ht,htx⟩ := ih p (by rw [hp,hpval]; omega)
    exact ⟨t,by omega,htx.trans hpx⟩

/-- An odd multiple-of-order displacement of the ternary total need not
preserve coin parity; an even displacement does, and can be refined. -/
theorem not_valid_ternary_powers_of_balanced_even_displacement
    {n : ℕ} {G : Type*} [AddCommGroup G] (a : G)
    (c : Fin n → ℤ) (hc : ∀ i, -1≤c i ∧ c i≤1)
    (hs : (∑ i,c i)≤0) (hpar : (∑ i,c i)%2=0)
    (hz : (∑ i,c i*(3:ℤ)^i.val) • a=0)
    (hne : (∑ i,c i*(3:ℤ)^i.val)≠0)
    (hweight : (n:ℤ) ≤ (∑ i : Fin n,(3:ℤ)^i.val)+(∑ i,c i*(3:ℤ)^i.val)) :
    ¬ ValidTuple (fun i : Fin n ↦ (3:ℕ)^i.val • a) := by
  classical
  intro hv
  let p : Fin n → ℕ := fun i ↦ (1+c i).toNat
  have hp (i) : (p i : ℤ)=1+c i := Int.toNat_of_nonneg (by have := hc i; omega)
  let s : Multiset (Fin n) := ∑ i,Multiset.replicate (p i) i
  have hcard : s.card=∑ i,p i := by simp [s]
  have hcardInt : (s.card : ℤ)=n+∑ i,c i := by
    rw [hcard]
    push_cast
    simp_rw [hp]
    simp [Finset.sum_add_distrib]
  have hsum : (s.map (fun i ↦ (3:ℕ)^i.val)).sum=∑ i,p i*(3:ℕ)^i.val := by
    exact (map_sum (Multiset.sumAddMonoidHom.comp (Multiset.mapAddMonoidHom (fun i : Fin n ↦ (3:ℕ)^i.val)))
      (fun i ↦ Multiset.replicate (p i) i) univ).trans (by simp)
  have hsumInt : (↑((s.map (fun i ↦ (3:ℕ)^i.val)).sum) : ℤ)=
      (∑ i : Fin n,(3:ℤ)^i.val)+(∑ i,c i*(3:ℤ)^i.val) := by
    rw [hsum]
    push_cast
    simp_rw [hp,add_mul,one_mul]
    rw [Finset.sum_add_distrib]
  have hle : s.card ≤ n := by omega
  have hpar' : s.card%2=n%2 := by omega
  obtain ⟨r,hr⟩ : ∃ r,n=s.card+2*r := ⟨(n-s.card)/2,by omega⟩
  have hpred : ∀ i : Fin n, 0 < i.val → ∃ j : Fin n, i.val=j.val+1 ∧ (3:ℕ)^i.val=3 • (3:ℕ)^j.val := by
    intro i hi
    refine ⟨⟨i.val-1,by omega⟩,by simp; omega,?_⟩
    change (3:ℕ)^i.val=3 • (3:ℕ)^(i.val-1)
    have heq : i.val = (i.val-1)+1 := by omega
    calc
      (3:ℕ)^i.val = (3:ℕ)^((i.val-1)+1) := congrArg _ heq
      _ = 3 • (3:ℕ)^(i.val-1) := by simp [pow_succ,Nat.mul_comm]
  obtain ⟨t,ht,htsum⟩ := exists_ranked_ternary_refinement Fin.val
    (fun i : Fin n ↦ (3:ℕ)^i.val) hpred s r (by omega)
  have hgroup : (t.map (fun i ↦ (3:ℕ)^i.val • a)).sum=∑ i : Fin n,(3:ℕ)^i.val • a := by
    have hv' : ((s.map (fun i ↦ (3:ℕ)^i.val)).sum : ℤ) • a=
        (∑ i : Fin n,(3:ℤ)^i.val) • a := by
      rw [hsumInt,add_zsmul,hz,add_zero]
    have htn : (t.map (fun i ↦ (3:ℕ)^i.val • a)).sum=(t.map (fun i ↦ (3:ℕ)^i.val)).sum • a := by
      clear ht htsum
      induction t using Multiset.induction_on with
      | empty => simp
      | cons i t ih => simp [ih,add_nsmul]
    rw [htn,htsum]
    have hcast : (∑ i : Fin n,(3:ℤ)^i.val) = ((∑ i : Fin n,(3:ℕ)^i.val : ℕ):ℤ) := by norm_cast
    rw [hcast] at hv'
    simpa only [natCast_zsmul,← Finset.sum_smul] using hv'
  have hall := multiset_count_eq_one_of_validTuple _ hv t (by omega) hgroup
  have htotal : (t.map (fun i ↦ (3:ℕ)^i.val)).sum=∑ i : Fin n,(3:ℕ)^i.val := by
    rw [Finset.sum_multiset_map_count]
    have hfull : t.toFinset=univ := Finset.eq_univ_of_forall (fun i ↦ by
      rw [Multiset.mem_toFinset,← Multiset.count_pos,hall]; omega)
    simp [hfull,hall]
  have hzero : (∑ i,c i*(3:ℤ)^i.val)=0 := by
    have hnat := htsum.symm.trans htotal
    have hint := congrArg (fun z : ℕ ↦ (z:ℤ)) hnat
    rw [hsumInt] at hint
    push_cast at hint
    omega
  exact hne hzero

/-- A valid initial ternary orbit segment forces every positive annihilator
above half the ternary total, up to the length correction for chain ends. -/
theorem sum_ternary_powers_lt_two_mul_add_length_of_valid
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (a : G) (hv : ValidTuple (fun i : Fin n ↦ 3^i.val • a))
    (d : ℕ) (hd : 0 < d) (hkill : d • a = 0) :
    (∑ i : Fin n, (3:ℕ)^i.val) < 2*d+n := by
  classical
  by_contra hsmall
  have hsmall' : 2*(d:ℤ)+n ≤ ∑ i : Fin n,(3:ℤ)^i.val := by
    exact_mod_cast (show 2*d+n ≤ ∑ i : Fin n,(3:ℕ)^i.val by omega)
  have hbound : |2*(d:ℤ)| ≤ ∑ i : Fin n,(3:ℤ)^i.val := by
    rw [abs_of_nonneg (by positivity)]
    omega
  obtain ⟨c,hc,he⟩ := exists_balanced_ternary_coefficients n (2*d) hbound
  have heven : (∑ i,c i)%2=0 := by
    have hmod : (∑ i,c i*(3:ℤ)^i.val) ≡ (∑ i,c i) [ZMOD 2] := by
      apply Int.ModEq.sum
      intro i _
      simpa using (Int.ModEq.refl (c i)).mul ((show (3:ℤ) ≡ 1 [ZMOD 2] by decide).pow i.val)
    change _%2=_%2 at hmod
    rw [he] at hmod
    omega
  by_cases hs : (∑ i,c i) ≤ 0
  · exact not_valid_ternary_powers_of_balanced_even_displacement a c hc hs heven
      (by rw [he,mul_smul,natCast_zsmul,hkill,smul_zero])
      (by rw [he]; omega) (by rw [he]; omega) hv
  · have hneg : (∑ i,(-c i)*(3:ℤ)^i.val) = -(2*(d:ℤ)) := by
      simp only [neg_mul,Finset.sum_neg_distrib,he]
    exact not_valid_ternary_powers_of_balanced_even_displacement a (fun i ↦ -c i)
      (fun i ↦ by have := hc i; omega)
      (by rw [Finset.sum_neg_distrib]; omega)
      (by rw [Finset.sum_neg_distrib]; omega)
      (by rw [hneg,neg_smul,mul_smul,natCast_zsmul,hkill,smul_zero,neg_zero])
      (by rw [hneg]; omega) (by rw [hneg]; omega) hv

/-- Beyond the first two exponents, a ternary power dominates the
next binary power with a spare unit. -/
theorem two_pow_succ_add_one_le_three_pow {n : ℕ} (hn : 2 ≤ n) :
    2^(n+1)+1 ≤ 3^n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [pow_succ (3:ℕ),pow_succ (2:ℕ)]
    omega

/-- The ternary total dominates twice the critical odd binary modulus,
including the length correction, starting in dimension three. -/
theorem two_pow_succ_add_length_le_ternary_sum_add_six
    {n : ℕ} (hn : 3 ≤ n) :
    2^(n+1)+n ≤ (∑ i : Fin n,(3:ℕ)^i.val)+6 := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    have hpow := two_pow_succ_add_one_le_three_pow (n:=n) (by omega)
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last]
    rw [pow_succ (2:ℕ)]
    omega

/-- An initial ternary orbit segment obeys an exponential modulus bound
without any closure or oddness hypothesis. -/
theorem ternary_segment_modulus_bound {n N : ℕ} [NeZero N]
    (a : ZMod N) (hv : ValidTuple (fun i : Fin n ↦ 3^i.val • a)) :
    3^n+1 ≤ 4*N+2*n := by
  have h := sum_ternary_powers_lt_two_mul_add_length_of_valid a hv N
    (NeZero.pos N) (by simp [nsmul_eq_mul])
  have hsum := two_mul_sum_ternary_powers_add_one n
  omega

/-- G2 holds for all valid initial ternary orbit segments at odd moduli. -/
theorem odd_stratum_lower_bound_of_ternary_segment {n N : ℕ}
    (hN : Odd N) (a : ZMod N)
    (hv : ValidTuple (fun i : Fin n ↦ 3^i.val • a)) :
    2^n-1 ≤ N := by
  haveI : NeZero N := ⟨hN.pos.ne'⟩
  by_cases hn : 3 ≤ n
  · have h := sum_ternary_powers_lt_two_mul_add_length_of_valid a hv N
      hN.pos (by simp [nsmul_eq_mul])
    have hb := two_pow_succ_add_length_le_ternary_sum_add_six hn
    rw [pow_succ] at hb
    obtain ⟨m,hm⟩ : ∃ m,n=m+1 := ⟨n-1,by omega⟩
    have hp : 2^n=2^m*2 := by rw [hm,pow_succ]
    have hpos : 0 < 2^n := by positivity
    obtain ⟨k,hk⟩ := hN
    omega
  · have hcases : n=0 ∨ n=1 ∨ n=2 := by omega
    rcases hcases with rfl | rfl | rfl
    · simp
    · have := hN.pos
      norm_num
      omega
    · have hb : 2 ≤ N := by simpa only [ZMod.card,Nat.reducePow] using card_ge _ hv
      obtain ⟨k,hk⟩ := hN
      norm_num
      omega

/-- Translation and reindexing preserve validity of a ternary segment. -/
theorem validTuple_ternary_segment_of_affine_representation
    {n : ℕ} {G : Type*} [AddCommGroup G]
    (g : Fin n → G) (hg : ValidTuple g) (e : Equiv.Perm (Fin n))
    (a b : G) (hseg : ∀ i,g (e i)=3^i.val • a+b) :
    ValidTuple (fun i : Fin n ↦ 3^i.val • a) := by
  have h := validTuple_sub_const (fun i ↦ g (e i))
    (validTuple_embedding e.toEmbedding g hg) b
  simpa only [hseg,add_sub_cancel_right] using h

/-- The ternary segment modulus bound is invariant under translation
and a permutation of the original coordinates. -/
theorem affine_ternary_segment_modulus_bound
    {n N : ℕ} [NeZero N] (g : Fin n → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin n)) (a b : ZMod N)
    (hseg : ∀ i,g (e i)=3^i.val • a+b) :
    3^n+1 ≤ 4*N+2*n :=
  ternary_segment_modulus_bound a
    (validTuple_ternary_segment_of_affine_representation g hg e a b hseg)

/-- G2 holds for valid affine ternary orbit segments in any coordinate order. -/
theorem odd_stratum_lower_bound_of_affine_ternary_segment
    {n N : ℕ} (hN : Odd N) (g : Fin n → ZMod N) (hg : ValidTuple g)
    (e : Equiv.Perm (Fin n)) (a b : ZMod N)
    (hseg : ∀ i,g (e i)=3^i.val • a+b) :
    2^n-1 ≤ N :=
  odd_stratum_lower_bound_of_ternary_segment hN a
    (validTuple_ternary_segment_of_affine_representation g hg e a b hseg)

end MinModulus
