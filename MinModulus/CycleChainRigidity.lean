import MinModulus.CycleFibreCapacity

/-!
# Extract logarithmic chain length beside a zero-sum fibre

Splitting a binary coin into two predecessors realizes every cardinality
between the initial coin count and its total weight. A k-coordinate
actual doubling chain therefore realizes its own sum with every count
from k to 2^k-1. If a disjoint nonempty zero-sum m-fibre exists, validity
forces 2^k <= m+k: otherwise the chain alone replaces the whole tuple.
This extraction holds in every abelian group, without criticality.

For an actual affine doubling cycle plus one outside chain, the extracted
logarithmic size bound closes the global, odd, every exact-stratum, and
exceptional-lift bounds in all dimensions. Component lengths are not
assumed small. The cycle-and-chain structure is still an explicit
hypothesis, not extracted from arbitrary tuples; G1/G2/G3 remain open.
-/

namespace MinModulus
open Finset

/-- Repeatedly splitting a binary coin into two predecessors attains
every cardinality between the starting count and its total weight. -/
theorem exists_binary_coin_refinement
    {k W : ℕ} (s : Multiset (Fin k))
    (hsum : (s.map (fun i ↦ 2^i.val)).sum=W) {K : ℕ} (hK : s.card ≤ K) (hW : K ≤ W) :
    ∃ t : Multiset (Fin k), t.card=K ∧ (t.map (fun i ↦ 2^i.val)).sum=W := by
  induction K, hK using Nat.le_induction with
  | base => exact ⟨s,rfl,hsum⟩
  | succ K hK ih =>
    obtain ⟨t,ht,hvalue⟩ := ih (by omega)
    have hpos : ∃ i ∈ t, 0 < i.val := by
      by_contra hnone
      push Not at hnone
      have hmap : t.map (fun i ↦ 2^i.val)=Multiset.replicate t.card 1 := by
        rw [← Multiset.map_const']
        apply Multiset.map_congr rfl
        intro i hi
        have hi0 : i.val=0 := by have := hnone i hi; omega
        simp [hi0]
      rw [hmap,Multiset.sum_replicate,smul_eq_mul,mul_one,ht] at hvalue
      omega
    obtain ⟨i,hi,hipos⟩ := hpos
    obtain ⟨u,hu⟩ := Multiset.exists_cons_of_mem hi
    let j : Fin k := ⟨i.val-1,by omega⟩
    have hpow : 2^i.val=2^j.val+2^j.val := by
      have he : i.val=j.val+1 := by dsimp [j]; omega
      rw [he,pow_succ']
      omega
    refine ⟨j ::ₘ j ::ₘ u,?_,?_⟩
    · rw [hu] at ht
      simp only [Multiset.card_cons] at ht ⊢
      omega
    · rw [hu] at hvalue
      simpa only [Multiset.map_cons,Multiset.sum_cons,hpow,add_assoc] using hvalue

/-- The initial k binary powers have total weight 2^k-1. -/
theorem sum_binary_powers (k : ℕ) : (∑ i : Fin k, 2^i.val)=2^k-1 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih]
    rw [pow_succ']
    have hp : 0 < 2^k := by positivity
    omega

/-- A full binary chain admits every coin count from its length up
to 2^k-1, without changing its actual group-valued sum. -/
theorem exists_doubling_chain_multiset_card
    {k K : ℕ} (hK : k ≤ K) (hupper : K ≤ 2^k-1)
    {G : Type*} [AddCommGroup G] (x : G) :
    ∃ s : Multiset (Fin k), s.card=K ∧
      (s.map (fun i ↦ 2^i.val • x)).sum=∑ i : Fin k, 2^i.val • x := by
  classical
  have htotal : ((Finset.univ : Finset (Fin k)).val.map (fun i ↦ 2^i.val)).sum=2^k-1 := by
    change (∑ i : Fin k, 2^i.val)=2^k-1
    exact sum_binary_powers k
  obtain ⟨s,hs,hvalue⟩ := exists_binary_coin_refinement (Finset.univ : Finset (Fin k)).val
    htotal (by simpa using hK) hupper
  refine ⟨s,hs,?_⟩
  have hmap (s : Multiset (Fin k)) :
      (s.map (fun i ↦ 2^i.val • x)).sum=(s.map (fun i ↦ 2^i.val)).sum • x := by
    induction s using Multiset.induction_on with
    | empty => simp
    | cons i s ih => simp only [Multiset.map_cons,Multiset.sum_cons,ih,add_nsmul]
  rw [hmap,hvalue]
  have hu := hmap (Finset.univ : Finset (Fin k)).val
  change (∑ i : Fin k, 2^i.val • x)=(∑ i : Fin k, 2^i.val) • x at hu
  rw [sum_binary_powers] at hu
  exact hu.symm

/-- A disjoint zero-sum fibre and doubling chain force a logarithmic
chain length. Otherwise chain splitting replaces the ENTIRE zero-sum
fibre at the original tuple length, producing an actual omitted rival. -/
theorem two_pow_chain_le_length_of_valid_zero_sum_fibre
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hzero : (∑ i : Fin m, g (Fin.castAdd k i))=0)
    (x : G) (hchain : ∀ j : Fin k, g (Fin.natAdd m j)=2^j.val • x) :
    2^k ≤ m+k := by
  classical
  by_contra hnot
  have hupper : m+k ≤ 2^k-1 := by omega
  obtain ⟨s,hs,hvalue⟩ := exists_doubling_chain_multiset_card (by omega : k ≤ m+k) hupper x
  let f : Fin k → Fin (m+k) := Fin.natAdd m
  let a : Fin (m+k) := Fin.castAdd k (⟨0,hm⟩ : Fin m)
  have hsum : ((s.map f).map g).sum=∑ i, g i := by
    rw [Fin.sum_univ_add,hzero,zero_add,Multiset.map_map]
    simpa only [Function.comp_def,f,hchain] using hvalue
  apply not_validTuple_of_multiset_omission g (s.map f)
    (by simpa only [Multiset.card_map] using hs) hsum a ?_ hg
  intro ha
  obtain ⟨j,_,hja⟩ := Multiset.mem_map.mp ha
  have hv := congrArg Fin.val hja
  simp only [f,a,Fin.val_natAdd,Fin.val_castAdd] at hv
  omega

/-- An actual affine cycle and a disjoint complete outside chain force
the logarithmic size hypothesis needed by cycle-fibre capacity. This
extraction is valid in every abelian group, without criticality. -/
theorem logarithmic_chain_of_valid_affine_cycle_chain
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b x : G) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b)
    (hchain : ∀ j, g (E (Fin.natAdd m j))+b=2^j.val • x) :
    k ≤ Nat.log 2 (m+k) := by
  have hv : ValidTuple (fun i ↦ g (E i)+b) := by
    simpa only [sub_neg_eq_add] using
      validTuple_sub_const (fun i ↦ g (E i)) (validTuple_embedding E.toEmbedding g hg) (-b)
  have hdouble : ∀ i, g (E (Fin.castAdd k (R i)))+b=2 • (g (E (Fin.castAdd k i))+b) := by
    intro i
    rw [hd]
    simp only [two_nsmul]
    abel
  have hzero : (∑ i : Fin m, (g (E (Fin.castAdd k i))+b))=0 :=
    sum_eq_zero_of_doubling_invariant R (fun i ↦ g (E (Fin.castAdd k i))+b) hdouble Finset.univ (by simp)
  have hpow := two_pow_chain_le_length_of_valid_zero_sum_fibre hm _ hv hzero x hchain
  exact (Nat.le_log_iff_pow_le (by omega) (by omega)).mpr hpow

/-- Full GLOBAL bound for an actual affine cycle plus one outside
chain, with no assumed size restriction on either component. -/
theorem global_lower_bound_of_valid_affine_cycle_chain
    {m k N : ℕ} [NeZero N] (hm : 2 ≤ m)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b x : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b)
    (hchain : ∀ j, g (E (Fin.natAdd m j))+b=2^j.val • x) :
    globalBound (m+k) ≤ N :=
  global_lower_bound_of_valid_large_affine_doubling_cycle hm
    (logarithmic_chain_of_valid_affine_cycle_chain (by omega) g hg E b x R hd hchain) g hg E b R hd

/-- Every exact stratum is closed for the same cycle-plus-chain class;
the outside-dimension restriction is extracted, not a new hypothesis. -/
theorem stratum_lower_bound_of_valid_affine_cycle_chain
    {m k s q : ℕ} (hm : 2 ≤ m) (hq : Odd q)
    (g : Fin (m+k) → ZMod (2^s*q)) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b x : ZMod (2^s*q)) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b)
    (hchain : ∀ j, g (E (Fin.natAdd m j))+b=2^j.val • x) :
    stratumBound (m+k) s ≤ 2^s*q :=
  stratum_lower_bound_of_valid_large_affine_doubling_cycle hm
    (logarithmic_chain_of_valid_affine_cycle_chain (by omega) g hg E b x R hd hchain) hq g hg E b R hd

/-- Direct odd-stratum endpoint, for arbitrary cycle and chain lengths. -/
theorem odd_lower_bound_of_valid_affine_cycle_chain
    {m k N : ℕ} (hm : 2 ≤ m) (hN : Odd N)
    (g : Fin (m+k) → ZMod N) (hg : ValidTuple g)
    (E : Equiv.Perm (Fin (m+k))) (b x : ZMod N) (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b)
    (hchain : ∀ j, g (E (Fin.natAdd m j))+b=2^j.val • x) :
    2^(m+k)-1 ≤ N := by
  have h := stratum_lower_bound_of_valid_affine_cycle_chain (m := m) (k := k) (s := 0) (q := N) hm hN
  rw [show (2 : ℕ)^0*N=N by simp] at h
  simpa [stratumBound] using h g hg E b x R hd hchain

/-- Direct exceptional-lift exclusion for the same unrestricted-length
cycle-plus-chain class. No unrestricted global gate is assumed. -/
theorem not_validTuple_exceptional_of_affine_cycle_chain
    {m k : ℕ} (hm : 2 ≤ m) (hnpow : 2^Nat.log 2 (m+k) ≠ m+k)
    (g : Fin (m+k) → ZMod (2*globalBound (m+k-1)))
    (E : Equiv.Perm (Fin (m+k))) (b x : ZMod (2*globalBound (m+k-1)))
    (R : Equiv.Perm (Fin m))
    (hd : ∀ i, g (E (Fin.castAdd k (R i)))=2 • g (E (Fin.castAdd k i))+b)
    (hchain : ∀ j, g (E (Fin.natAdd m j))+b=2^j.val • x) :
    ¬ ValidTuple g := by
  intro hg
  exact not_validTuple_exceptional_of_large_affine_doubling_cycle hm
    (logarithmic_chain_of_valid_affine_cycle_chain (by omega) g hg E b x R hd hchain)
    hnpow g E b R hd hg

end MinModulus
