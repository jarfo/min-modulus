import MinModulus.CycleShortSumRigidity
import MinModulus.FullCoverExpansionExtraction
import MinModulus.ActualFibreMixedRivals

/-!
# Complete outside spectrum of a mapped Mersenne cycle

Validity is characterized by all outside multisets, including those that
cannot be reached by squarefree one-coin rewrites. Intermediate surpluses
have unique sparse cycle targets; the full-length outside layer omits the
original total. No bound on the outside dimension is imposed.
-/

namespace MinModulus
open Finset

/-- An injectively mapped binary Mersenne cycle is valid. -/
theorem validTuple_mapped_mersenne_powers
    {m : ℕ} (hm : 2 ≤ m) {G : Type*} [AddCommGroup G]
    (τ : ZMod (2^m-1) →+ G) (hτ : Function.Injective τ) :
    ValidTuple (fun i : Fin m ↦ τ ((2^i.val : ℕ) : ZMod (2^m-1))) := by
  have hbase : ValidTuple (fun i : Fin m ↦ (a i.val : ZMod (2^m-1))) :=
    validTuple_fixed_of_valid (by simpa using valid_gap hm (t := 0) (by simpa using (by omega : 1 ≤ m)))
  have ht := validTuple_sub_const _ hbase (-1)
  have hp (i : Fin m) : (a i.val : ZMod (2^m-1))-(-1)=((2^i.val : ℕ) : ZMod (2^m-1)) := by
    rw [a, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one]
    abel
  simp only [hp] at ht
  exact validTuple_comp ht τ hτ

/-- Every outside multiset of surplus r has a unique sparse cycle
target whenever its discrepancy enters the cycle subgroup. -/
theorem outside_multiset_surplus_unique_sparse_target
    {m k r : ℕ} [NeZero (2^m-1)] {G : Type*} [AddCommGroup G]
    (hr : 0 < r) (hrm : r < m) (τ : ZMod (2^m-1) →+ G)
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1)))
    (p : Multiset (Fin k)) (hp : p.card=k+r) (z : ZMod (2^m-1))
    (hz : (p.map (fun i ↦ g (Fin.natAdd m i))).sum-(∑ i, g (Fin.natAdd m i))=τ z) :
    ∃! S : Finset (Fin m), S.card < r ∧ τ z=∑ i ∈ S, g (Fin.castAdd k i) := by
  classical
  let c : Fin k → ℤ := fun i ↦ (p.count i : ℤ)-1
  have hc (i : Fin k) : -1 ≤ c i := by dsimp [c]; omega
  have hcount : (∑ i : Fin k, p.count i)=k+r := by
    rw [Multiset.sum_count_eq_card (fun i _ ↦ Finset.mem_univ i), hp]
  have hcsum : (∑ i, c i)=(r : ℤ) := by
    simp only [c, Finset.sum_sub_distrib, ← Nat.cast_sum, hcount,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one,
      Nat.cast_add]
    omega
  have hweight : (∑ i : Fin k, p.count i • g (Fin.natAdd m i))=
      (p.map (fun i ↦ g (Fin.natAdd m i))).sum := by
    rw [Finset.sum_multiset_map_count]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hzero : p.count i=0 := Multiset.count_eq_zero.mpr (by simpa using hi)
    simp [hzero]
  apply outside_surplus_unique_sparse_target_of_valid_mersenne_cycle hr hrm τ g hg hpref c hc hcsum z
  simpa only [c, sub_smul, natCast_zsmul, one_smul, Finset.sum_sub_distrib, hweight] using hz

/-- The outside-only full-length layer cannot contain the original
outside total beside a nonempty zero-sum prefix. -/
theorem outside_full_length_sum_ne_total_of_valid_zero_sum_prefix
    {m k : ℕ} (hm : 0 < m) {G : Type*} [AddCommGroup G]
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hzero : (∑ i : Fin m, g (Fin.castAdd k i))=0)
    (p : Multiset (Fin k)) (hp : p.card=m+k) :
    (p.map (fun i ↦ g (Fin.natAdd m i))).sum ≠ ∑ i, g (Fin.natAdd m i) := by
  intro hv
  let a : Fin (m+k) := Fin.castAdd k (⟨0,hm⟩ : Fin m)
  apply not_validTuple_of_multiset_omission g (p.map (Fin.natAdd m))
    (by simpa only [Multiset.card_map] using hp) ?_ a ?_ hg
  · simpa only [Multiset.map_map, Function.comp_def, Fin.sum_univ_add, hzero, zero_add] using hv
  · intro ha
    obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp ha
    have he := congrArg Fin.val hi
    simp only [a, Fin.val_castAdd, Fin.val_natAdd] at he
    omega

/-- Complete criterion for an arbitrary outside tuple beside an actual
mapped Mersenne cycle. It covers every multiset through the full parent
length, including multisets unreachable by one-coin expansion paths. -/
theorem validTuple_iff_mapped_cycle_outside_spectrum
    {m k d : ℕ} (hm : 2 ≤ m) [NeZero d] [NeZero (2^m-1)]
    (τ : ZMod (2^m-1) →+ ZMod (d*(2^m-1))) (hτ : Function.Injective τ)
    (g : Fin (m+k) → ZMod (d*(2^m-1)))
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) :
    let q : Fin k → ZMod d := fun i ↦
      ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d) (g (Fin.natAdd m i))
    ValidTuple g ↔
      (∀ p : Multiset (Fin k), p.card ≤ k → (p.map q).sum=∑ i, q i →
        p=(Finset.univ : Finset (Fin k)).val) ∧
      (∀ r : ℕ, 0 < r → r < m → ∀ p : Multiset (Fin k), p.card=k+r →
        ∀ z : ZMod (2^m-1),
          (p.map (fun i ↦ g (Fin.natAdd m i))).sum-(∑ i, g (Fin.natAdd m i))=τ z →
          ∃ S : Finset (Fin m), S.card < r ∧ τ z=∑ i ∈ S, g (Fin.castAdd k i)) ∧
      (∀ p : Multiset (Fin k), p.card=m+k →
        (p.map (fun i ↦ g (Fin.natAdd m i))).sum ≠ ∑ i, g (Fin.natAdd m i)) := by
  classical
  letI : NeZero (d*(2^m-1)) := ⟨Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _)⟩
  let π := ZMod.castHom (dvd_mul_right d (2^m-1)) (ZMod d)
  let q : Fin k → ZMod d := fun i ↦ π (g (Fin.natAdd m i))
  let x : Fin m → ZMod (d*(2^m-1)) := fun i ↦ g (Fin.castAdd k i)
  have hx : ValidTuple x := by
    simpa only [x, hpref] using validTuple_mapped_mersenne_powers hm τ hτ
  have hzero : (∑ i, x i)=0 := by
    simp only [x, hpref, ← map_sum]
    rw [← Nat.cast_sum, sum_binary_powers, ZMod.natCast_self, map_zero]
  change ValidTuple g ↔ _
  constructor
  · intro hg
    refine ⟨?_, ?_, outside_full_length_sum_ne_total_of_valid_zero_sum_prefix (by omega) g hg hzero⟩
    · intro p hp hv
      exact quotient_multiset_eq_of_card_le_of_actual_fibre_cover (by omega) τ hτ g hg
        (fun i : Fin m ↦ ((2^i.val : ℕ) : ZMod (2^m-1))) hpref
        (exists_power_multiset_sum_at_mersenne hm) Finset.univ p (by simpa using hp) hv
    · intro r hr hrm p hp z hz
      exact (outside_multiset_surplus_unique_sparse_target hr hrm τ g hg hpref p hp z hz).exists
  · rintro ⟨hmin, hsparse, hlast⟩ c hc hv
    let p : Multiset (Fin k) := ∑ i, Multiset.replicate (c (Fin.natAdd m i)) i
    have hp : p.card=∑ i, c (Fin.natAdd m i) := by simp [p]
    have hpv : (p.map (fun i ↦ g (Fin.natAdd m i))).sum=
        ∑ i, c (Fin.natAdd m i) • g (Fin.natAdd m i) := by
      have haux (A : Finset (Fin k)) :
          ((∑ i ∈ A, Multiset.replicate (c (Fin.natAdd m i)) i).map
            (fun i ↦ g (Fin.natAdd m i))).sum=
          ∑ i ∈ A, c (Fin.natAdd m i) • g (Fin.natAdd m i) := by
        induction A using Finset.induction_on with
        | empty => simp
        | @insert a A ha ih => simp [Finset.sum_insert, ha, Multiset.map_add, Multiset.sum_add, ih]
      exact haux Finset.univ
    obtain ⟨s, hs, hsv⟩ := exists_multiset_sum_card_of_nat_weights
      x (fun i ↦ c (Fin.castAdd k i))
    have hcard : s.card+p.card=m+k := by
      simpa only [Fin.sum_univ_add, hp, hs] using hc
    have hvalue : (s.map x).sum+(p.map (fun i ↦ g (Fin.natAdd m i))).sum=
        ∑ i, g (Fin.natAdd m i) := by
      simpa only [Fin.sum_univ_add, hpv, hsv, show (∑ i : Fin m, g (Fin.castAdd k i))=0 from hzero,
        zero_add, x] using hv
    have hπx (i : Fin m) : π (x i)=0 := by
      obtain ⟨β, _, hfactor⟩ := exists_bijective_scale_factor_of_injective_cyclic_hom τ hτ
      change π (g (Fin.castAdd k i))=0
      rw [hpref, ← hfactor]
      rw [← ZMod.natCast_zmod_val (β ((2^i.val : ℕ) : ZMod (2^m-1))), zmodScaleHom_natCast]
      simp only [π, Nat.cast_mul, map_mul, map_natCast, ZMod.natCast_self, zero_mul]
    have hq : (p.map q).sum=∑ i, q i := by
      have h := congrArg π hvalue
      simpa only [map_add, map_multiset_sum, Multiset.map_map, Function.comp_def,
        hπx, Multiset.map_const', Multiset.sum_replicate, nsmul_zero, zero_add, map_sum, q] using h
    have heq : p=(Finset.univ : Finset (Fin k)).val := by
      by_cases hpk : p.card ≤ k
      · exact hmin p hpk hq
      have hple : p.card ≤ m+k := by omega
      by_cases hfull : p.card=m+k
      · have hs0 : s=0 := Multiset.card_eq_zero.mp (by omega)
        exact False.elim (hlast p hfull (by simpa [hs0] using hvalue))
      let r := p.card-k
      have hr : 0 < r := by dsimp [r]; omega
      have hrm : r < m := by dsimp [r]; omega
      have hpr : p.card=k+r := by dsimp [r]; omega
      have hscard : s.card=m-r := by omega
      have hker : π ((p.map (fun i ↦ g (Fin.natAdd m i))).sum-(∑ i, g (Fin.natAdd m i)))=0 := by
        simp only [map_sub, map_multiset_sum, Multiset.map_map, Function.comp_def, map_sum]
        change (p.map q).sum-(∑ i, q i)=0
        rw [hq, sub_self]
      obtain ⟨z, hz⟩ := exists_cyclic_hom_preimage_of_castHom_eq_zero τ hτ _ hker
      obtain ⟨S, hS, hSv⟩ := hsparse r hr hrm p hpr z hz.symm
      have hneg : (s.map x).sum= -τ z := by rw [hz]; exact eq_neg_of_add_eq_zero_left (by rw [sub_eq_add_neg]; rw [← add_assoc, hvalue, add_neg_cancel])
      exact False.elim ((mersenne_short_cover_iff_not_sparse_sum hr hrm τ x hx hpref z).mp
        ⟨s, hscard, hneg⟩ ⟨S, hS, hSv.symm⟩)
    have hpcard : p.card=k := by simp [heq]
    have hpvalue : (p.map (fun i ↦ g (Fin.natAdd m i))).sum=∑ i, g (Fin.natAdd m i) := by
      rw [heq]; rfl
    have hprefix : (∑ i, c (Fin.castAdd k i) • x i)=∑ i, x i := by
      rw [hpvalue] at hvalue
      have ht : (s.map x).sum=0 := add_right_cancel (hvalue.trans (zero_add _).symm)
      rwa [hsv, ← hzero] at ht
    have hleft := hx (fun i ↦ c (Fin.castAdd k i)) (by omega) hprefix
    have hright (i : Fin k) : c (Fin.natAdd m i)=1 := by
      have h := congrArg (Multiset.count i) heq
      have hci : p.count i=c (Fin.natAdd m i) := by
        simp [p, Multiset.count_sum', Multiset.count_replicate]
      have hone : (Finset.univ : Finset (Fin k)).val.count i=1 :=
        Multiset.count_eq_one_of_mem (Finset.univ : Finset (Fin k)).nodup (Finset.mem_univ i)
      simpa only [hci, hone] using h
    intro i
    exact Fin.addCases hleft hright i

/-- Actual cycle-subgroup discrepancies attained by outside multisets
with exactly r extra coins. This records values, not representations. -/
noncomputable def mappedCycleOutsideSurplusTargets
    {m k : ℕ} [NeZero (2^m-1)] {G : Type*} [AddCommGroup G]
    (τ : ZMod (2^m-1) →+ G) (g : Fin (m+k) → G) (r : ℕ) :
    Finset (ZMod (2^m-1)) := by
  classical
  exact Finset.univ.filter (fun z ↦ ∃ p : Multiset (Fin k), p.card=k+r ∧
    (p.map (fun i ↦ g (Fin.natAdd m i))).sum-(∑ i, g (Fin.natAdd m i))=τ z)

/-- All attained targets in an intermediate outside layer fit inside
the exact binomial set of sparse cycle sums. Different representations
may coincide; no injectivity of the outside multiset map is assumed. -/
theorem card_mappedCycleOutsideSurplusTargets_le_binomial
    {m k r : ℕ} [NeZero (2^m-1)] {G : Type*} [AddCommGroup G]
    (hr : 0 < r) (hrm : r < m) (τ : ZMod (2^m-1) →+ G) (hτ : Function.Injective τ)
    (g : Fin (m+k) → G) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m, g (Fin.castAdd k i)=τ ((2^i.val : ℕ) : ZMod (2^m-1))) :
    (mappedCycleOutsideSurplusTargets τ g r).card ≤ ∑ j ∈ Finset.range r, m.choose j := by
  classical
  let x : Fin m → G := fun i ↦ g (Fin.castAdd k i)
  let K := (Finset.range r).biUnion (fun j ↦ (Finset.univ : Finset (Fin m)).powersetCard j)
  have hsub : (mappedCycleOutsideSurplusTargets τ g r).image τ ⊆
      K.image (fun S ↦ ∑ i ∈ S, x i) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨p, hp, hpv⟩ := (Finset.mem_filter.mp hz).2
    obtain ⟨S, ⟨hS, hSv⟩, _⟩ := outside_multiset_surplus_unique_sparse_target hr hrm τ g hg hpref p hp z hpv
    apply Finset.mem_image.mpr
    refine ⟨S, ?_, hSv.symm⟩
    exact Finset.mem_biUnion.mpr ⟨S.card, Finset.mem_range.mpr hS,
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ S, rfl⟩⟩
  have hx : ValidTuple x := validTuple_embedding ⟨Fin.castAdd k, Fin.castAdd_injective m k⟩ g hg
  have hzero : (∑ i, x i)=0 := by
    simp only [x, hpref, ← map_sum]
    rw [← Nat.cast_sum, sum_binary_powers, ZMod.natCast_self, map_zero]
  have hpred (i : Fin m) : ∃ j, x i=2 • x j := by
    obtain ⟨j, hj⟩ := mersenne_power_doubling_predecessor (by omega) i
    exact ⟨j, by simpa only [x, hpref, map_nsmul] using congrArg τ hj⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hτ] at hc
  exact hc.trans_eq (card_small_subset_sums_of_valid_zero_sum_predecessors x hx hzero hpred (by omega))

end MinModulus
