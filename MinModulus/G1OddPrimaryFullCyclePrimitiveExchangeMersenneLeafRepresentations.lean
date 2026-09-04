/-
# Exact multiset representations on a pointed Mersenne leaf

The canonical pointed leaf cycle in the exact-Mersenne C1 residual is an
affine copy of the super-increasing digits.  The exact digit-sum theorem from
`UniqueSums` therefore represents every nonzero element of the cyclic leaf
direction by a rival size-`d` multiset on those leaves.

This module makes that passage explicit in three reusable layers: a natural
multiset equality, its signed `Witness` form, and zero-extension to the
ambient tuple along an injective pointed leaf map.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneFiveExternalRows

namespace MinModulus

open Finset

variable {G : Type*} [AddCommGroup G]

/-- An affine Mersenne leaf cycle realizes every nonzero cyclic target as a
size-`d` multiset difference. -/
theorem exists_mersenneLeaf_exactMultisetRepresentation
    {d s : ℕ} (hd : 3 ≤ d) (hs0 : 0 < s) (hsq : s < 2 ^ d - 1)
    (root v : G) (hv : addOrderOf v = 2 ^ d - 1)
    (h : Fin d → G) (hnormal : ∀ i, h i = root + a i.val • v) :
    ∃ k : Fin d → ℕ,
      (∑ i, k i) = d ∧
      (∑ i, k i • h i) = (∑ i, h i) + s • v := by
  obtain ⟨k₀, hk₀, hkval⟩ :=
    exists_exact_dsum_rep_modEq_mersenne hd hs0 hsq
  let k : Fin d → ℕ := fun i ↦ k₀ i.val
  have hksum : (∑ i, k i) = d := by
    rw [Fin.sum_univ_eq_sum_range]
    exact hk₀
  let A : ℕ := ∑ i : Fin d, k i * a i.val
  let U : ℕ := ∑ i : Fin d, a i.val
  have hkA : A + d = val d k₀ := by
    have h := sum_a_add_dsum d k₀
    rw [hk₀] at h
    change (∑ i : Fin d, k₀ i.val * a i.val) + d = val d k₀
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ k₀ i * a i) d]
    exact h
  have hdones : dsum d (fun _ ↦ 1) = d := by
    simp [dsum]
  have hvones : val d (fun _ ↦ 1) = 2 ^ d - 1 := by
    unfold val
    simpa only [one_mul] using sum_two_pow d
  have hUA : U + d = 2 ^ d - 1 := by
    have h := sum_a_add_dsum d (fun _ ↦ 1)
    rw [hdones, hvones] at h
    change (∑ i : Fin d, a i.val) + d = 2 ^ d - 1
    rw [Fin.sum_univ_eq_sum_range a d]
    simpa only [one_mul] using h
  have hcoeffmod : A ≡ U + s [MOD 2 ^ d - 1] := by
    apply Nat.ModEq.add_right_cancel' d
    rw [hkA]
    have hperiod : (2 ^ d - 1) + s ≡ s [MOD 2 ^ d - 1] := by
      have hm : (2 ^ d - 1) * 1 + s ≡ s [MOD 2 ^ d - 1] :=
        Nat.ModEq.modulus_mul_add
      simpa only [mul_one] using hm
    have hrhs : U + s + d = (2 ^ d - 1) + s := by omega
    rw [hrhs]
    exact hkval.trans hperiod.symm
  have hcoeffsmul : A • v = (U + s) • v := by
    have hmods : A % (2 ^ d - 1) = (U + s) % (2 ^ d - 1) := hcoeffmod
    rw [← mod_addOrderOf_nsmul v A,
      ← mod_addOrderOf_nsmul v (U + s), hv, hmods]
  refine ⟨k, hksum, ?_⟩
  calc
    (∑ i, k i • h i) =
        (∑ i, k i • (root + a i.val • v)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hnormal]
    _ = ∑ i, (k i • root + k i • (a i.val • v)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [nsmul_add]
    _ = (∑ i, k i • root) + (∑ i, (k i * a i.val) • v) := by
          rw [Finset.sum_add_distrib]
          apply congrArg (fun z ↦ (∑ i, k i • root) + z)
          apply Finset.sum_congr rfl
          intro i _
          rw [mul_comm, mul_nsmul]
    _ = d • root + A • v := by
          have hroot : (∑ i, k i • root) = (∑ i, k i) • root :=
            Finset.sum_nsmul_assoc Finset.univ k root
          have hvsum : (∑ i, (k i * a i.val) • v) = A • v :=
            Finset.sum_nsmul_assoc Finset.univ
              (fun i ↦ k i * a i.val) v
          rw [hroot, hvsum, hksum]
    _ = d • root + (U + s) • v := by rw [hcoeffsmul]
    _ = d • root + U • v + s • v := by rw [add_nsmul]; abel
    _ = Finset.univ.sum
          (fun i : Fin d ↦ root + a (Fin.val i) • v) + s • v := by
          have hroot : (∑ _i : Fin d, root) = d • root := by
            simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          have hvsum : (∑ i : Fin d, a (Fin.val i) • v) = U • v :=
            Finset.sum_nsmul_assoc Finset.univ
              (fun i : Fin d ↦ a (Fin.val i)) v
          rw [Finset.sum_add_distrib, hroot, hvsum]
    _ = (∑ i, h i) + s • v := by
          apply congrArg (fun z ↦ z + s • v)
          apply Finset.sum_congr rfl
          intro i _
          rw [hnormal]

/-- Witness form of `exists_mersenneLeaf_exactMultisetRepresentation`. -/
theorem exists_mersenneLeaf_witness
    {d s : ℕ} (hd : 3 ≤ d) (hs0 : 0 < s) (hsq : s < 2 ^ d - 1)
    (root v : G) (hv : addOrderOf v = 2 ^ d - 1)
    (h : Fin d → G) (hnormal : ∀ i, h i = root + a i.val • v) :
    ∃ c : Fin d → ℤ, Witness h (s • v) c := by
  obtain ⟨k, hksum, hkval⟩ :=
    exists_mersenneLeaf_exactMultisetRepresentation
      hd hs0 hsq root v hv h hnormal
  let c : Fin d → ℤ := fun i ↦ (k i : ℤ) - 1
  have hcsum : (∑ i, c i) = 0 := by
    simp only [c, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    have hcast : (∑ i, (k i : ℤ)) = (d : ℤ) := by
      rw [← Nat.cast_sum, hksum]
    omega
  have hcval : (∑ i, c i • h i) = s • v := by
    calc
      (∑ i, c i • h i) = ∑ i, (k i • h i - h i) := by
        apply Finset.sum_congr rfl
        intro i _
        change ((k i : ℤ) - 1) • h i = k i • h i - h i
        rw [sub_zsmul, one_zsmul, natCast_zsmul]
        exact (sub_eq_add_neg _ _).symm
      _ = (∑ i, k i • h i) - ∑ i, h i := by
        change Finset.univ.sum (fun i : Fin d ↦ k i • h i - h i) =
          Finset.univ.sum (fun i : Fin d ↦ k i • h i) -
            Finset.univ.sum h
        rw [Finset.sum_sub_distrib]
      _ = s • v := by rw [hkval]; abel
  have htarget : s • v ≠ 0 := by
    intro hz
    have hdvd : 2 ^ d - 1 ∣ s := by
      rw [← hv, addOrderOf_dvd_iff_nsmul_eq_zero]
      exact hz
    exact (Nat.not_le_of_lt hsq) (Nat.le_of_dvd hs0 hdvd)
  refine ⟨c, ?_, ?_, hcsum, hcval⟩
  · intro hc
    have hzero : (∑ i, c i • h i) = 0 := by simp [hc]
    exact htarget (hcval.symm.trans hzero)
  · intro i
    dsimp only [c]
    omega

/-- Extend the leaf witness by zero along an injective pointed leaf map. -/
theorem exists_mersenneLeaf_ambientWitness
    {n d s : ℕ} (hd : 3 ≤ d) (hs0 : 0 < s) (hsq : s < 2 ^ d - 1)
    (root v : G) (hv : addOrderOf v = 2 ^ d - 1)
    (g : Fin n → G) (leaf : Fin d → Fin n)
    (hleaf : Function.Injective leaf) (e : Fin d ≃ Fin d)
    (hnormal : ∀ i,
      g (leaf (e i)) = root + a i.val • v) :
    ∃ c : Fin n → ℤ, Witness g (s • v) c := by
  let emb : Fin d ↪ Fin n :=
    ⟨fun i ↦ leaf (e i), hleaf.comp e.injective⟩
  obtain ⟨c, hc⟩ := exists_mersenneLeaf_witness
    hd hs0 hsq root v hv (fun i ↦ g (emb i)) hnormal
  exact ⟨Function.extend emb c (fun _ ↦ 0),
    (witness_extend_embedding_iff emb g c).2 hc⟩

end MinModulus
