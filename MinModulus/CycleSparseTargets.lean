import MinModulus.CycleThinCover
import MinModulus.Descent

/-!
# Sparse targets for arbitrary outside surplus

A shortened binary-cycle cover has a uniform description of its holes.
Consequently, in a valid tuple containing a mapped Mersenne cycle, an
outside coefficient vector bounded below by -1 and having total k,
with 0 < k < cycle length, can enter the cycle subgroup only at a sum
of fewer than k distinct cycle entries. This extends the previous
one- and two-coordinate lifting arguments to arbitrary outside support.

The cycle is actual input structure. These lemmas do not extract one
from an arbitrary critical tuple or discharge the full G1/G2/G3 gates.
-/

namespace MinModulus
open Finset

/-- A shortened Mersenne coin cover fails only at sums of fewer than the
missing number of distinct cycle entries. -/
theorem mersenne_short_cover_or_sparse_sum
    {m k : ℕ} [NeZero (2 ^ m - 1)] (hk : 0 < k) (hkm : k < m)
    (z : ZMod (2 ^ m - 1)) :
    (∃ s : Multiset (Fin m), s.card = m - k ∧
      (s.map (fun i ↦ ((2 ^ i.val : ℕ) : ZMod (2 ^ m - 1)))).sum = -z) ∨
    (∃ S : Finset (Fin m), S.card < k ∧
      (∑ i ∈ S, ((2 ^ i.val : ℕ) : ZMod (2 ^ m - 1))) = z) := by
  classical
  by_cases hz : z = 0
  · exact Or.inr ⟨∅, by simpa using hk, by simp [hz]⟩
  have hneg : -z ≠ 0 := neg_ne_zero.mpr hz
  have hval := (-z).val_lt
  obtain ⟨S, hS⟩ := exists_binary_subset_of_lt_two_pow
    (by omega : (-z).val < 2 ^ m)
  have hsumS : (∑ i ∈ S, ((2 ^ i.val : ℕ) : ZMod (2 ^ m - 1))) = -z := by
    rw [← Nat.cast_sum, hS, ZMod.natCast_zmod_val]
  by_cases hsmall : S.card ≤ m - k
  · have hpos : 0 < S.card := by
      by_contra hnot
      have hempty : S = ∅ := Finset.card_eq_zero.mp (by omega)
      rw [hempty, Finset.sum_empty] at hsumS
      exact hneg hsumS.symm
    obtain ⟨s, hs, hvalue⟩ := exists_multiset_card_ge_of_doubling_predecessors
      (fun i : Fin m ↦ ((2 ^ i.val : ℕ) : ZMod (2 ^ m - 1)))
      (mersenne_power_doubling_predecessor (by omega)) S.val hpos hsmall
    exact Or.inl ⟨s, hs, hvalue.trans hsumS⟩
  · have hcard := Finset.card_compl_add_card S
    simp only [Fintype.card_fin] at hcard
    refine Or.inr ⟨Sᶜ, by omega, ?_⟩
    have hsum := Finset.sum_compl_add_sum S
      (fun i : Fin m ↦ ((2 ^ i.val : ℕ) : ZMod (2 ^ m - 1)))
    have hall : (∑ i : Fin m, ((2 ^ i.val : ℕ) : ZMod (2 ^ m - 1))) = 0 := by
      rw [← Nat.cast_sum, sum_binary_powers, ZMod.natCast_self]
    rw [hsumS, hall] at hsum
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg] using hsum)

/-- Outside coefficients with surplus k can hit a Mersenne-cycle subgroup
only at sums of fewer than k distinct cycle entries. The coefficients may
be arbitrary integers above -1; they need not form a subset or a pair. -/
theorem outside_surplus_sparse_target_of_valid_mersenne_cycle
    {m n k : ℕ} [NeZero (2 ^ m - 1)]
    {G : Type*} [AddCommGroup G]
    (hk : 0 < k) (hkm : k < m)
    (τ : ZMod (2 ^ m - 1) →+ G)
    (g : Fin (m + n) → G) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m,
      g (Fin.castAdd n i) = τ ((2 ^ i.val : ℕ) : ZMod (2 ^ m - 1)))
    (c : Fin n → ℤ) (hc : ∀ j, -1 ≤ c j) (hsum : (∑ j, c j) = k)
    (z : ZMod (2 ^ m - 1))
    (hvalue : (∑ j, c j • g (Fin.natAdd m j)) = τ z) :
    ∃ S : Finset (Fin m), S.card < k ∧
      τ z = ∑ i ∈ S, g (Fin.castAdd n i) := by
  classical
  rcases mersenne_short_cover_or_sparse_sum hk hkm z with ⟨s, hs, htarget⟩ | ⟨S, hS, hz⟩
  · let delta : Fin m → ℤ := fun i ↦ (s.count i : ℤ) - 1
    have hcount : (∑ i : Fin m, s.count i) = m - k := by
      rw [Multiset.sum_count_eq_card (fun i _ ↦ Finset.mem_univ i)]
      exact hs
    have hdeltaSum : (∑ i, delta i) = -(k : ℤ) := by
      dsimp [delta]
      rw [Finset.sum_sub_distrib, ← Nat.cast_sum, hcount]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one, Nat.cast_sub (by omega : k ≤ m)]
      omega
    have hcycle : (∑ i : Fin m, g (Fin.castAdd n i)) = 0 := by
      simp only [hpref, ← map_sum]
      rw [← Nat.cast_sum, sum_binary_powers, ZMod.natCast_self, map_zero]
    have hsweight : (∑ i : Fin m, s.count i • g (Fin.castAdd n i)) = -τ z := by
      have heq : (∑ i : Fin m, s.count i • g (Fin.castAdd n i)) =
          (s.map (fun i ↦ g (Fin.castAdd n i))).sum := by
        rw [Finset.sum_multiset_map_count]
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hi0 : s.count i = 0 := Multiset.count_eq_zero.mpr (by simpa using hi)
        simp [hi0]
      rw [heq]
      simp only [hpref]
      simpa only [map_multiset_sum, Multiset.map_map, Function.comp_def, map_neg]
        using congrArg τ htarget
    have hdeltaValue : (∑ i, delta i • g (Fin.castAdd n i)) = -τ z := by
      simp only [delta, sub_smul, natCast_zsmul, one_smul, Finset.sum_sub_distrib,
        hsweight, hcycle, sub_zero]
    let C : Fin (m + n) → ℤ := Fin.addCases delta c
    have hleft (i : Fin m) : C (Fin.castAdd n i) = delta i := by simp [C]
    have hright (j : Fin n) : C (Fin.natAdd m j) = c j := by simp [C]
    apply False.elim
    apply (validTuple_iff_no_zero_witness g).mp hg C
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hzero
      have hczero : c = 0 := by
        funext j
        have h := congrFun hzero (Fin.natAdd m j)
        simpa only [hright, Pi.zero_apply] using h
      simp only [hczero, Pi.zero_apply, Finset.sum_const_zero] at hsum
      omega
    · intro i
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
      · rw [hleft]
        dsimp [delta]
        omega
      · rw [hright]
        exact hc j
    · rw [Fin.sum_univ_add]
      simp only [hleft, hright, hdeltaSum, hsum, neg_add_cancel]
    · rw [Fin.sum_univ_add]
      simp only [hleft, hright, hdeltaValue, hvalue, neg_add_cancel]
  · refine ⟨S, hS, ?_⟩
    rw [← hz, map_sum]
    simp only [hpref]

/-- Every one-unit-surplus outside relation in the quotient lifts to an
actual zero relation; no two-coordinate support condition is needed. -/
theorem outside_one_surplus_target_eq_zero_of_valid_mersenne_cycle
    {m n : ℕ} [NeZero (2 ^ m - 1)]
    {G : Type*} [AddCommGroup G] (hm : 2 ≤ m)
    (τ : ZMod (2 ^ m - 1) →+ G)
    (g : Fin (m + n) → G) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m,
      g (Fin.castAdd n i) = τ ((2 ^ i.val : ℕ) : ZMod (2 ^ m - 1)))
    (c : Fin n → ℤ) (hc : ∀ j, -1 ≤ c j) (hsum : (∑ j, c j) = 1)
    (z : ZMod (2 ^ m - 1))
    (hvalue : (∑ j, c j • g (Fin.natAdd m j)) = τ z) : τ z = 0 := by
  obtain ⟨S, hS, htarget⟩ := outside_surplus_sparse_target_of_valid_mersenne_cycle
    (by omega : 0 < 1) (by omega : 1 < m) τ g hg hpref c hc hsum z hvalue
  have hempty : S = ∅ := Finset.card_eq_zero.mp (by omega)
  simpa only [hempty, Finset.sum_empty] using htarget

/-- Two units of outside surplus can hit the cycle subgroup only at zero
or one actual cycle entry, irrespective of the number of outside coordinates. -/
theorem outside_two_surplus_target_zero_or_entry_of_valid_mersenne_cycle
    {m n : ℕ} [NeZero (2 ^ m - 1)]
    {G : Type*} [AddCommGroup G] (hm : 3 ≤ m)
    (τ : ZMod (2 ^ m - 1) →+ G)
    (g : Fin (m + n) → G) (hg : ValidTuple g)
    (hpref : ∀ i : Fin m,
      g (Fin.castAdd n i) = τ ((2 ^ i.val : ℕ) : ZMod (2 ^ m - 1)))
    (c : Fin n → ℤ) (hc : ∀ j, -1 ≤ c j) (hsum : (∑ j, c j) = 2)
    (z : ZMod (2 ^ m - 1))
    (hvalue : (∑ j, c j • g (Fin.natAdd m j)) = τ z) :
    τ z = 0 ∨ ∃ i : Fin m, τ z = g (Fin.castAdd n i) := by
  obtain ⟨S, hS, htarget⟩ := outside_surplus_sparse_target_of_valid_mersenne_cycle
    (by omega : 0 < 2) (by omega : 2 < m) τ g hg hpref c hc hsum z hvalue
  by_cases hempty : S.card = 0
  · have hset : S = ∅ := Finset.card_eq_zero.mp hempty
    exact Or.inl (by simpa only [hset, Finset.sum_empty] using htarget)
  · obtain ⟨i, hi⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
    exact Or.inr ⟨i, by simpa only [hi, Finset.sum_singleton] using htarget⟩

end MinModulus
