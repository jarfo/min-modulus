import MinModulus.TightQuotientCube
import Mathlib.Data.Nat.BitIndices
import Mathlib.Data.Finset.Fin

/-!
# Thin Mersenne-cycle covers and actual outside relations

Binary supports and cyclic predecessor splitting construct covers with
one or two fewer coins. These covers lift quotient doubling relations
between outside coordinates to actual equalities, without assuming that
an arbitrary critical tuple has such a cycle or a full-cover fibre.
-/

namespace MinModulus
open Finset

/-- In a doubling-predecessor-closed set, every nonempty multiset
can be expanded to any larger cardinality at unchanged actual sum. -/
theorem exists_multiset_card_ge_of_doubling_predecessors
    {α G : Type*} [AddCommGroup G] (x : α → G)
    (hpred : ∀ i, ∃ j, x i=2 • x j)
    (s : Multiset α) (hs : 0 < s.card) {K : ℕ} (hK : s.card ≤ K) :
    ∃ t : Multiset α, t.card=K ∧ (t.map x).sum=(s.map x).sum := by
  induction K, hK using Nat.le_induction with
  | base => exact ⟨s,rfl,rfl⟩
  | succ K hK ih =>
    obtain ⟨t,ht,hvalue⟩ := ih
    have htne : t ≠ 0 := by intro hz; simp [hz] at ht; omega
    have hdecomp : t=0 ∨ ∃ i u, t=i ::ₘ u :=
      Multiset.induction_on t (Or.inl rfl) (fun i u _ ↦ Or.inr ⟨i,u,rfl⟩)
    rcases hdecomp with hz | ⟨i,u,rfl⟩
    · exact (htne hz).elim
    obtain ⟨j,hj⟩ := hpred i
    refine ⟨j ::ₘ j ::ₘ u,by simp only [Multiset.card_cons] at ht ⊢; omega,?_⟩
    simpa only [Multiset.map_cons,Multiset.sum_cons,hj,two_nsmul,add_assoc] using hvalue

/-- Every natural number below 2^m is the sum of an ACTUAL subset
of the first m binary powers. -/
theorem exists_binary_subset_of_lt_two_pow
    {m n : ℕ} (hn : n < 2^m) :
    ∃ S : Finset (Fin m), (∑ i ∈ S, 2^i.val)=n := by
  classical
  let X : Finset ℕ := ⟨(n.bitIndices : Multiset ℕ),by simp⟩
  have hsmall : ∀ i ∈ X, i < m := by
    intro i hi
    have hbit : i ∈ n.bitIndices := hi
    have hle := Nat.two_pow_le_of_mem_bitIndices hbit
    by_contra hnot
    have hp := Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) (by omega : m ≤ i)
    omega
  have hsum : (∑ i ∈ X, 2^i)=n := by
    change (n.bitIndices.map (fun i ↦ 2^i)).sum=n
    exact Nat.sum_map_two_pow_bitIndices n
  refine ⟨X.attachFin hsmall,?_⟩
  rw [← Finset.image_val_attachFin hsmall] at hsum
  rw [Finset.sum_image (fun _ _ _ _ h ↦ Fin.ext h)] at hsum
  exact hsum

/-- Binary powers form a predecessor-closed cycle modulo a Mersenne
number, including the actual last-to-first wrap. -/
theorem mersenne_power_doubling_predecessor
    {m : ℕ} (hm : 0 < m) [NeZero (2^m-1)] (i : Fin m) :
    ∃ j : Fin m, ((2^i.val : ℕ) : ZMod (2^m-1))=
      2 • ((2^j.val : ℕ) : ZMod (2^m-1)) := by
  by_cases hi : i.val=0
  · let j : Fin m := ⟨m-1,by omega⟩
    have hj : m=j.val+1 := by dsimp [j]; omega
    have hp : ((2^m : ℕ) : ZMod (2^m-1))=1 := by
      have hz := ZMod.natCast_self (2^m-1)
      rw [Nat.cast_sub Nat.one_le_two_pow,Nat.cast_one] at hz
      exact sub_eq_zero.mp hz
    refine ⟨j,?_⟩
    have he : (2 : ℕ)^m=2*2^j.val := by
      calc
        _=2^(j.val+1) := congrArg (fun a : ℕ ↦ 2^a) hj
        _=2*2^j.val := pow_succ' _ _
    calc
      _=1 := by rw [hi,pow_zero,Nat.cast_one]
      _=((2^m : ℕ) : ZMod (2^m-1)) := hp.symm
      _=((2*2^j.val : ℕ) : ZMod (2^m-1)) := congrArg (fun a : ℕ ↦ (a : ZMod (2^m-1))) he
      _=2 • ((2^j.val : ℕ) : ZMod (2^m-1)) := by simp only [Nat.cast_mul,Nat.cast_ofNat,nsmul_eq_mul]
  · let j : Fin m := ⟨i.val-1,by omega⟩
    have hj : i.val=j.val+1 := by dsimp [j]; omega
    refine ⟨j,?_⟩
    rw [hj,pow_succ']
    simp only [Nat.cast_mul,Nat.cast_ofNat,nsmul_eq_mul]

/-- With m-2 coins the Mersenne cycle covers every residue except
zero and the negatives of its own entries. The support bound and
actual multiset are constructed uniformly, not by a residue census. -/
theorem exists_power_multiset_card_sub_two_except_cycle_holes
    {m : ℕ} (hm : 3 ≤ m) [NeZero (2^m-1)] (z : ZMod (2^m-1))
    (hz : z ≠ 0) (hholes : ∀ i : Fin m, z ≠ -((2^i.val : ℕ) : ZMod (2^m-1))) :
    ∃ s : Multiset (Fin m), s.card=m-2 ∧
      (s.map (fun i ↦ ((2^i.val : ℕ) : ZMod (2^m-1)))).sum=z := by
  classical
  have hzlt := z.val_lt
  obtain ⟨S,hS⟩ := exists_binary_subset_of_lt_two_pow (by omega : z.val < 2^m)
  have hScard := Finset.card_le_univ S
  simp only [Fintype.card_fin] at hScard
  have hcomcard := Finset.card_compl_add_card S
  simp only [Fintype.card_fin] at hcomcard
  have hcomsum : (∑ i ∈ Sᶜ, 2^i.val)+z.val=2^m-1 := by
    rw [← hS,Finset.sum_compl_add_sum]
    exact sum_binary_powers m
  have hsmall : S.card ≤ m-2 := by
    by_contra hnot
    have hccard : Sᶜ.card ≤ 1 := by omega
    by_cases hc0 : Sᶜ.card=0
    · have hempty := Finset.card_eq_zero.mp hc0
      rw [hempty,Finset.sum_empty,zero_add] at hcomsum
      omega
    · have hc1 : Sᶜ.card=1 := by omega
      obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hc1
      rw [hi,Finset.sum_singleton] at hcomsum
      have hcast := congrArg (fun a : ℕ ↦ (a : ZMod (2^m-1))) hcomsum
      simp only [Nat.cast_add,ZMod.natCast_zmod_val,ZMod.natCast_self] at hcast
      apply hholes i
      exact eq_neg_of_add_eq_zero_right hcast
  have hpos : 0 < S.card := by
    by_contra hnot
    have hs0 : S=∅ := Finset.card_eq_zero.mp (by omega)
    rw [hs0,Finset.sum_empty] at hS
    apply hz
    rw [← ZMod.natCast_zmod_val z,← hS,Nat.cast_zero]
  obtain ⟨t,ht,hvalue⟩ := exists_multiset_card_ge_of_doubling_predecessors
    (fun i : Fin m ↦ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (mersenne_power_doubling_predecessor (by omega)) S.val hpos hsmall
  refine ⟨t,ht,?_⟩
  rw [hvalue]
  change (∑ i ∈ S, ((2^i.val : ℕ) : ZMod (2^m-1)))=z
  rw [← Nat.cast_sum,hS,ZMod.natCast_zmod_val]

/-- With m-1 coins the Mersenne cycle covers EVERY nonzero residue. -/
theorem exists_power_multiset_card_pred_of_ne_zero
    {m : ℕ} (hm : 2 ≤ m) [NeZero (2^m-1)] (z : ZMod (2^m-1)) (hz : z ≠ 0) :
    ∃ s : Multiset (Fin m), s.card=m-1 ∧
      (s.map (fun i ↦ ((2^i.val : ℕ) : ZMod (2^m-1)))).sum=z := by
  classical
  have hzlt := z.val_lt
  obtain ⟨S,hS⟩ := exists_binary_subset_of_lt_two_pow (by omega : z.val < 2^m)
  have hScard := Finset.card_le_univ S
  simp only [Fintype.card_fin] at hScard
  have hsmall : S.card ≤ m-1 := by
    by_contra hnot
    have hcard : S.card=m := by omega
    have hfull : S=Finset.univ := Finset.eq_of_subset_of_card_le (Finset.subset_univ S) (by simpa using hcard.ge)
    rw [hfull,sum_binary_powers] at hS
    omega
  have hpos : 0 < S.card := by
    by_contra hnot
    have hs0 : S=∅ := Finset.card_eq_zero.mp (by omega)
    rw [hs0,Finset.sum_empty] at hS
    apply hz
    rw [← ZMod.natCast_zmod_val z,← hS,Nat.cast_zero]
  obtain ⟨t,ht,hvalue⟩ := exists_multiset_card_ge_of_doubling_predecessors
    (fun i : Fin m ↦ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (mersenne_power_doubling_predecessor (by omega)) S.val hpos hsmall
  refine ⟨t,ht,?_⟩
  rw [hvalue]
  change (∑ i ∈ S, ((2^i.val : ℕ) : ZMod (2^m-1)))=z
  rw [← Nat.cast_sum,hS,ZMod.natCast_zmod_val]

/-- If an outside double lies in an actual mapped Mersenne-cycle
subgroup, validity forces it to be zero or an ACTUAL cycle entry.
The m-2 cover constructs a three-copy outside rival otherwise. -/
theorem double_extra_eq_zero_or_cycle_of_valid_mapped_mersenne_cycle
    {m : ℕ} (hm : 3 ≤ m) [NeZero (2^m-1)]
    {G : Type*} [AddCommGroup G] (τ : ZMod (2^m-1) →+ G)
    (g : Fin (m+1) → G) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g i.castSucc=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hdouble : ∃ z, τ z=2 • g (Fin.last m)) :
    2 • g (Fin.last m)=0 ∨ ∃ i : Fin m, g i.castSucc=2 • g (Fin.last m) := by
  classical
  by_contra hnot
  push Not at hnot
  obtain ⟨z,hz⟩ := hdouble
  have hz0 : -z ≠ 0 := by
    intro heq
    have hz0 : z=0 := neg_eq_zero.mp heq
    exact hnot.1 (hz.symm.trans (by rw [hz0,map_zero]))
  have hholes (i : Fin m) : -z ≠ -((2^i.val : ℕ) : ZMod (2^m-1)) := by
    intro heq
    have he : z=((2^i.val : ℕ) : ZMod (2^m-1)) := neg_injective heq
    apply hnot.2 i
    rw [hpref,← he,hz]
  obtain ⟨s,hs,hvalue⟩ := exists_power_multiset_card_sub_two_except_cycle_holes hm (-z) hz0 hholes
  have hcycle : (∑ i : Fin m, g i.castSucc)=0 := by
    simp only [hpref,← map_sum]
    rw [← Nat.cast_sum,sum_binary_powers,ZMod.natCast_self,map_zero]
  let t := s.map Fin.castSucc+Multiset.replicate 3 (Fin.last m)
  have hcard : t.card=m+1 := by
    simp only [t,Multiset.card_add,Multiset.card_map,Multiset.card_replicate,hs]
    omega
  have hmap : ((s.map Fin.castSucc).map g).sum=τ (-z) := by
    simp only [Multiset.map_map,Function.comp_def,hpref]
    simpa only [map_multiset_sum,Multiset.map_map,Function.comp_def] using congrArg τ hvalue
  have hsum : (t.map g).sum=∑ i, g i := by
    rw [Fin.sum_univ_castSucc,hcycle,zero_add]
    simp only [t,Multiset.map_add,Multiset.sum_add,Multiset.map_replicate,
      Multiset.sum_replicate,hmap,map_neg,hz]
    simp only [show (3 : ℕ)=2+1 by decide,add_nsmul,one_nsmul]
    abel
  have hlast : Fin.last m ∉ s.map Fin.castSucc := by
    intro hmem
    obtain ⟨i,_,heq⟩ := Multiset.mem_map.mp hmem
    exact Fin.castSucc_ne_last i heq
  have hc := multiset_count_eq_one_of_validTuple g hg t hcard hsum (Fin.last m)
  norm_num [t,Multiset.count_eq_zero.mpr hlast] at hc

/-- A quotient doubling relation between two outside coordinates
lifts to an ACTUAL doubling relation beside a mapped Mersenne cycle.
Any nonzero subgroup discrepancy is covered with m-1 cycle coins
and gives a three-copy first-outside rival omitting the second. -/
theorem extra_eq_double_of_valid_mapped_mersenne_cycle
    {m : ℕ} (hm : 2 ≤ m) [NeZero (2^m-1)]
    {G : Type*} [AddCommGroup G] (τ : ZMod (2^m-1) →+ G)
    (g : Fin (m+2) → G) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd 2 i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (hrel : ∃ z, τ z=2 • g (Fin.natAdd m (0 : Fin 2))-g (Fin.natAdd m (1 : Fin 2))) :
    g (Fin.natAdd m (1 : Fin 2))=2 • g (Fin.natAdd m (0 : Fin 2)) := by
  classical
  by_contra hnot
  obtain ⟨z,hz⟩ := hrel
  have hz0 : -z ≠ 0 := by
    intro heq
    have hz0 : z=0 := neg_eq_zero.mp heq
    apply hnot
    apply Eq.symm
    apply sub_eq_zero.mp
    rw [← hz,hz0,map_zero]
  obtain ⟨s,hs,hvalue⟩ := exists_power_multiset_card_pred_of_ne_zero hm (-z) hz0
  have hcycle : (∑ i : Fin m, g (Fin.castAdd 2 i))=0 := by
    simp only [hpref,← map_sum]
    rw [← Nat.cast_sum,sum_binary_powers,ZMod.natCast_self,map_zero]
  let x : Fin (m+2) := Fin.natAdd m (0 : Fin 2)
  let y : Fin (m+2) := Fin.natAdd m (1 : Fin 2)
  let t := s.map (Fin.castAdd 2)+Multiset.replicate 3 x
  have hcard : t.card=m+2 := by
    simp only [t,Multiset.card_add,Multiset.card_map,Multiset.card_replicate,hs]
    omega
  have hmap : ((s.map (Fin.castAdd 2)).map g).sum=τ (-z) := by
    simp only [Multiset.map_map,Function.comp_def,hpref]
    simpa only [map_multiset_sum,Multiset.map_map,Function.comp_def] using congrArg τ hvalue
  have hsum : (t.map g).sum=∑ i, g i := by
    rw [Fin.sum_univ_add,hcycle,zero_add,Fin.sum_univ_two]
    simp only [t,Multiset.map_add,Multiset.sum_add,Multiset.map_replicate,
      Multiset.sum_replicate,hmap,map_neg,hz,x]
    simp only [show (3 : ℕ)=2+1 by decide,add_nsmul,one_nsmul]
    abel
  have hxy : y ≠ x := by
    intro heq
    have he := congrArg Fin.val heq
    simp only [x,y,Fin.val_natAdd,Fin.val_zero,Fin.val_one,add_zero] at he
    omega
  have hy : y ∉ s.map (Fin.castAdd 2) := by
    intro hmem
    obtain ⟨i,_,heq⟩ := Multiset.mem_map.mp hmem
    have he := congrArg Fin.val heq
    simp only [y,Fin.val_castAdd,Fin.val_natAdd,Fin.val_one] at he
    omega
  have hc := multiset_count_eq_one_of_validTuple g hg t hcard hsum y
  norm_num [t,Multiset.count_eq_zero.mpr hy,hxy] at hc

end MinModulus
