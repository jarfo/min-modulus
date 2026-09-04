/-
# Signed binary arithmetic of the antipodal subset residual

The exact-negative antipodal branch now consists of two disjoint,
equal-cardinality subsets of the pointed affine Mersenne leaf.  Pulling those
sets back through the pointed orbit cancels the common affine root.  The
remaining target equation is an equality of natural multiples of a generator
of order `2^d-1`.

Both subset values lie strictly below that order.  Consequently the signed
binary difference has only the two expected integer representatives: `s` or
`s-(2^d-1)`.  This module proves that reduction uniformly in `d`.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneAntipodalSubsets

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- Pull an ambient coordinate subset back through a pointed leaf
enumeration. -/
def pointedLeafSubset
    {n d : ℕ} (leaf : Fin d → Fin n) (e : Fin d ≃ Fin d)
    (P : Finset (Fin n)) : Finset (Fin d) :=
  Finset.univ.filter (fun i ↦ leaf (e i) ∈ P)

/-- A subset of the leaf image is recovered exactly after pointed pullback
and re-embedding. -/
theorem image_pointedLeafSubset_eq
    {n d : ℕ} (leaf : Fin d → Fin n) (e : Fin d ≃ Fin d)
    (P : Finset (Fin n))
    (hP : P ⊆ (Finset.univ : Finset (Fin d)).image leaf) :
    (pointedLeafSubset leaf e P).image (fun i ↦ leaf (e i)) = P := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact (Finset.mem_filter.mp hi).2
  · intro hj
    obtain ⟨k, _hk, hk⟩ := Finset.mem_image.mp (hP hj)
    apply Finset.mem_image.mpr
    refine ⟨e.symm k, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [e.apply_symm_apply] using (hk ▸ hj)
    · simpa only [e.apply_symm_apply] using hk

/-- Ordinary binary value of a subset of pointed leaf positions. -/
def binarySubsetValue {d : ℕ} (A : Finset (Fin d)) : ℕ :=
  ∑ i ∈ A, 2 ^ i.val

/-- The super-increasing digits `a_i=2^i-1` differ from ordinary binary
weights by one per chosen position. -/
theorem binarySubsetValue_eq_sum_a_add_card
    {d : ℕ} (A : Finset (Fin d)) :
    binarySubsetValue A = (∑ i ∈ A, a i.val) + A.card := by
  classical
  calc
    binarySubsetValue A = ∑ i ∈ A, (a i.val + 1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      simp only [a]
      exact (Nat.sub_add_cancel Nat.one_le_two_pow).symm
    _ = (∑ i ∈ A, a i.val) + A.card := by
      rw [Finset.sum_add_distrib]
      simp

/-- The complete arithmetic content of a pointed leaf subset residual.
After pullback, the binary subset difference represents either `s` or
`s-(2^d-1)` as an ordinary integer. -/
theorem LeafEqualCardSubsetDifference.exists_pointed_binary_arithmetic
    {n d s : ℕ} (hd : 3 ≤ d)
    (g : Fin n → G) (root v : G)
    (hv : addOrderOf v = 2 ^ d - 1)
    (leaf : Fin d → Fin n) (hleaf : Function.Injective leaf)
    (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v)
    (r : Fin n)
    (hr : leaf (e ⟨0, by omega⟩) = r)
    (hs0 : 0 < s) (hsq : s < 2 ^ d - 1)
    (hres : LeafEqualCardSubsetDifference g leaf (s • v) r) :
    ∃ A M : Finset (Fin d),
      Disjoint A M ∧ A.card = M.card ∧
      ⟨0, by omega⟩ ∈ A ∧
      (binarySubsetValue A = binarySubsetValue M + s ∨
        binarySubsetValue A + (2 ^ d - 1) =
          binarySubsetValue M + s) := by
  classical
  obtain ⟨P, N, hPsub, hNsub, hPNdisjoint, hPNcard, hrP, hvalue⟩ := hres
  let A := pointedLeafSubset leaf e P
  let M := pointedLeafSubset leaf e N
  let f : Fin d → Fin n := fun i ↦ leaf (e i)
  have hf : Function.Injective f := hleaf.comp e.injective
  have hAimage : A.image f = P := by
    exact image_pointedLeafSubset_eq leaf e P hPsub
  have hMimage : M.image f = N := by
    exact image_pointedLeafSubset_eq leaf e N hNsub
  have hAdisjointM : Disjoint A M := by
    rw [Finset.disjoint_left]
    intro i hiA hiM
    apply (Finset.disjoint_left.mp hPNdisjoint)
    · rw [← hAimage]
      exact Finset.mem_image.mpr ⟨i, hiA, rfl⟩
    · rw [← hMimage]
      exact Finset.mem_image.mpr ⟨i, hiM, rfl⟩
  have hAcardP : A.card = P.card := by
    calc
      A.card = (A.image f).card :=
        (Finset.card_image_of_injective A hf).symm
      _ = P.card := by rw [hAimage]
  have hMcardN : M.card = N.card := by
    calc
      M.card = (M.image f).card :=
        (Finset.card_image_of_injective M hf).symm
      _ = N.card := by rw [hMimage]
  have hAMcard : A.card = M.card := by
    rw [hAcardP, hMcardN]
    exact hPNcard
  have hzeroA : (⟨0, by omega⟩ : Fin d) ∈ A := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hr]
    exact hrP
  have hsumP : (∑ j ∈ P, g j) = ∑ i ∈ A, g (f i) := by
    rw [← hAimage, Finset.sum_image hf.injOn]
  have hsumN : (∑ j ∈ N, g j) = ∑ i ∈ M, g (f i) := by
    rw [← hMimage, Finset.sum_image hf.injOn]
  have hvalueAM :
      (∑ i ∈ A, g (f i)) = (∑ i ∈ M, g (f i)) + s • v := by
    rw [← hsumP, ← hsumN]
    exact hvalue
  let Avalue : ℕ := ∑ i ∈ A, a i.val
  let Mvalue : ℕ := ∑ i ∈ M, a i.val
  have hnormalA :
      (∑ i ∈ A, g (f i)) = A.card • root + Avalue • v := by
    calc
      (∑ i ∈ A, g (f i)) =
          ∑ i ∈ A, (root + a i.val • v) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact hnormal i
      _ = A.card • root + Avalue • v := by
        rw [Finset.sum_add_distrib, Finset.sum_const]
        apply congrArg (fun z ↦ A.card • root + z)
        exact Finset.sum_nsmul_assoc A (fun i ↦ a i.val) v
  have hnormalM :
      (∑ i ∈ M, g (f i)) = M.card • root + Mvalue • v := by
    calc
      (∑ i ∈ M, g (f i)) =
          ∑ i ∈ M, (root + a i.val • v) := by
            apply Finset.sum_congr rfl
            intro i _hi
            exact hnormal i
      _ = M.card • root + Mvalue • v := by
        rw [Finset.sum_add_distrib, Finset.sum_const]
        apply congrArg (fun z ↦ M.card • root + z)
        exact Finset.sum_nsmul_assoc M (fun i ↦ a i.val) v
  have hmul : Avalue • v = (Mvalue + s) • v := by
    have h := hvalueAM
    rw [hnormalA, hnormalM, hAMcard] at h
    have htail : Avalue • v = Mvalue • v + s • v := by
      apply add_left_cancel (a := M.card • root)
      simpa only [add_assoc] using h
    simpa only [add_nsmul] using htail
  have hq : 0 < 2 ^ d - 1 := by
    have hpow : 0 < 2 ^ (d - 3) := pow_pos (by norm_num) _
    rw [show d = 3 + (d - 3) by omega, pow_add]
    norm_num
    omega
  have htotal : (∑ i : Fin d, a i.val) + d = 2 ^ d - 1 := by
    have hdones : dsum d (fun _ ↦ 1) = d := by simp [dsum]
    have hvones : val d (fun _ ↦ 1) = 2 ^ d - 1 := by
      unfold val
      simpa only [one_mul] using sum_two_pow d
    have h := sum_a_add_dsum d (fun _ ↦ 1)
    rw [hdones, hvones] at h
    rw [Fin.sum_univ_eq_sum_range a d]
    simpa only [one_mul] using h
  have hAvalueLe : Avalue ≤ ∑ i : Fin d, a i.val := by
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ A)
  have hMvalueLe : Mvalue ≤ ∑ i : Fin d, a i.val := by
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ M)
  have hAvalueLt : Avalue < 2 ^ d - 1 := by omega
  have hMvalueLt : Mvalue < 2 ^ d - 1 := by omega
  have hzero :
      ((Avalue : ℤ) - ((Mvalue + s : ℕ) : ℤ)) • v = 0 := by
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul, hmul, add_neg_cancel]
  have hdvd : ((2 ^ d - 1 : ℕ) : ℤ) ∣
      (Avalue : ℤ) - ((Mvalue + s : ℕ) : ℤ) := by
    rw [← hv]
    exact addOrderOf_dvd_iff_zsmul_eq_zero.mpr hzero
  obtain ⟨z, hz⟩ := hdvd
  have hqInt : (0 : ℤ) < ((2 ^ d - 1 : ℕ) : ℤ) := by
    exact_mod_cast hq
  have hAvalueLtInt : (Avalue : ℤ) < ((2 ^ d - 1 : ℕ) : ℤ) := by
    exact_mod_cast hAvalueLt
  have hMvalueLtInt : (Mvalue : ℤ) < ((2 ^ d - 1 : ℕ) : ℤ) := by
    exact_mod_cast hMvalueLt
  have hs0Int : (0 : ℤ) < (s : ℤ) := by exact_mod_cast hs0
  have hsqInt : (s : ℤ) < ((2 ^ d - 1 : ℕ) : ℤ) := by
    exact_mod_cast hsq
  have hdiffLower :
      -2 * ((2 ^ d - 1 : ℕ) : ℤ) <
        (Avalue : ℤ) - ((Mvalue + s : ℕ) : ℤ) := by
    push_cast
    omega
  have hdiffUpper :
      (Avalue : ℤ) - ((Mvalue + s : ℕ) : ℤ) <
        ((2 ^ d - 1 : ℕ) : ℤ) := by
    push_cast
    omega
  have hzLower : (-2 : ℤ) < z := by nlinarith
  have hzUpper : z < 1 := by nlinarith
  have harith : Avalue = Mvalue + s ∨
      Avalue + (2 ^ d - 1) = Mvalue + s := by
    have hzCases : z = -1 ∨ z = 0 := by omega
    rcases hzCases with hzNeg | hzZero
    · right
      have hcast :
          ((Avalue + (2 ^ d - 1) : ℕ) : ℤ) =
            ((Mvalue + s : ℕ) : ℤ) := by
        rw [hzNeg] at hz
        push_cast
        norm_num at hz ⊢
        omega
      exact_mod_cast hcast
    · left
      have hcast : (Avalue : ℤ) = ((Mvalue + s : ℕ) : ℤ) := by
        rw [hzZero] at hz
        norm_num at hz
        omega
      exact_mod_cast hcast
  have hAbinary := binarySubsetValue_eq_sum_a_add_card A
  have hMbinary := binarySubsetValue_eq_sum_a_add_card M
  refine ⟨A, M, hAdisjointM, hAMcard, hzeroA, ?_⟩
  rcases harith with harith | harith
  · left
    dsimp only [Avalue, Mvalue] at harith
    omega
  · right
    dsimp only [Avalue, Mvalue] at harith
    omega

end MinModulus
