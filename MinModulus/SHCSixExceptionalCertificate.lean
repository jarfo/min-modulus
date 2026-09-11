/-
# Kernel-checked order-105 six-coordinate certificate

This file provides the trusted interface for the sole remaining
six-coordinate generator exception.  After unit scaling and sorting, the
distinguished coordinate is 3 and the other five coordinates form an
increasing selection from the 55 nonunits strictly above 3 in `ZMod 105`.
Generated files cover every such selection by either a subset-sum collision
or a forbidden head-2 relation.  Only the emitted ordinary kernel proofs
(`decide` and decision-assisted simplification) are trusted; the Torch code
used to find the compressed decision trees is not.
-/
import MinModulus.SHCSixGenerator
import Mathlib.Data.Fin.Tuple.Sort
import MinModulus.SHCSixExceptionalCertificateData

namespace MinModulus

open Finset

namespace SHCSixExceptionalCertificate

set_option maxRecDepth 100000

def maskSum {G : Type*} [AddCommMonoid G] (h : Fin 6 → G) (mask : ℕ) : G :=
  (if mask.testBit 0 then h 0 else 0) +
  (if mask.testBit 1 then h 1 else 0) +
  (if mask.testBit 2 then h 2 else 0) +
  (if mask.testBit 3 then h 3 else 0) +
  (if mask.testBit 4 then h 4 else 0) +
  (if mask.testBit 5 then h 5 else 0)

theorem maskSum_eq_sum {G : Type*} [AddCommMonoid G]
    (h : Fin 6 → G) (mask : ℕ) :
    maskSum h mask = ∑ i ∈ maskSet mask, h i := by
  simp only [maskSet, Finset.sum_filter]
  rw [Fin.sum_univ_six]
  simp [maskSum]
  rfl

def coveredNat (codes : List ℕ) (h : Fin 6 → ℕ) : Bool :=
  codes.any fun code ↦ relationZeroNat h code

theorem coveredNat_exists_valid (codes : List ℕ) (h : Fin 6 → ℕ)
    (hvalid : ∀ code ∈ codes, validRelationCode code)
    (hc : coveredNat codes h = true) : ∃ code,
      validRelationCode code ∧ relationZeroNat h code = true := by
  simp only [coveredNat, List.any_eq_true] at hc
  obtain ⟨code, hmem, hzero⟩ := hc
  exact ⟨code, hvalid code hmem, hzero⟩

theorem natCast_maskSumNat (h : Fin 6 → ℕ) (mask : ℕ) :
    ((maskSumNat h mask : ℕ) : ZMod 105) =
      maskSum (fun i ↦ (h i : ZMod 105)) mask := by
  simp [maskSumNat, maskSum]

theorem relationZeroNat_not_shc (h : Fin 6 → ℕ) (code : ℕ)
    (hvalid : validRelationCode code) (hzero : relationZeroNat h code = true) :
    ¬ SHC (fun i ↦ (h i : ZMod 105)) := by
  intro hs
  unfold validRelationCode at hvalid
  unfold relationZeroNat at hzero
  split at hvalid <;> split at hzero
  · simp only [decide_eq_true_eq] at hzero
    have heq : maskSum (fun i ↦ (h i : ZMod 105)) (code % 64) =
        maskSum (fun i ↦ (h i : ZMod 105)) (code / 64) := by
      rw [← natCast_maskSumNat, ← natCast_maskSumNat,
        ZMod.natCast_eq_natCast_iff]
      exact hzero
    rw [maskSum_eq_sum, maskSum_eq_sum] at heq
    exact hvalid (hs.dis heq)
  · omega
  · omega
  · simp only [decide_eq_true_eq] at hzero
    dsimp only at hvalid hzero
    have heqcast :
        ((2 * h ⟨(code - 4096) % 6, Nat.mod_lt _ (by norm_num)⟩ +
          maskSumNat h (((code - 4096) / 6) % 64) : ℕ) : ZMod 105) =
          (maskSumNat h (((code - 4096) / 6) / 64) : ZMod 105) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact hzero
    have heq :
        2 • ((h ⟨(code - 4096) % 6, Nat.mod_lt _ (by norm_num)⟩ : ℕ) : ZMod 105) +
          maskSum (fun i ↦ (h i : ZMod 105)) (((code - 4096) / 6) % 64) =
          maskSum (fun i ↦ (h i : ZMod 105)) (((code - 4096) / 6) / 64) := by
      rw [← natCast_maskSumNat, ← natCast_maskSumNat]
      simpa [Nat.cast_add, Nat.cast_mul, nsmul_eq_mul] using heqcast
    rw [maskSum_eq_sum, maskSum_eq_sum] at heq
    exact hs.sh2 _ _ _ hvalid.1 hvalid.2.1 hvalid.2.2.1 hvalid.2.2.2 heq

theorem nonunit105Value_strictMono : StrictMono nonunit105Value := by decide

theorem exists_nonunit105Index (z : ZMod 105) (hz3 : z ≠ 3)
    (hz0 : z ≠ 0) (hznu : ¬ IsUnit z) :
    ∃ i : Fin 55, nonunit105Value i = z.val := by
  revert z
  decide

def SortedNormalizedNonunitExcluded : Prop :=
  ∀ h : Fin 6 → ZMod 105, h 0 = 3 → Monotone (fun i ↦ (h i).val) →
    (∀ i, ¬ IsUnit (h i)) → ¬ SHC h

theorem sortedNormalizedNonunitExcluded_of_certificate
    (hcert : Certificate) : SortedNormalizedNonunitExcluded := by
  intro h h0 hmono hnonunit hs
  have hinj : Function.Injective (fun i ↦ (h i).val) := by
    intro i j hij
    have hh : h i = h j := by
      apply ZMod.val_injective
      exact hij
    have hsum : (∑ k ∈ ({i} : Finset (Fin 6)), h k) =
        ∑ k ∈ ({j} : Finset (Fin 6)), h k := by simp [hh]
    exact Finset.singleton_injective (hs.dis hsum)
  have hstrict : StrictMono (fun i ↦ (h i).val) := hmono.strictMono_of_injective hinj
  have hv0 : (h 0).val = 3 := by rw [h0]; decide
  have htail_exists : ∀ i : Fin 5, ∃ j : Fin 55,
      nonunit105Value j = (h i.succ).val := by
    intro i
    apply exists_nonunit105Index
    · intro heq
      have hh : h i.succ = h 0 := by simpa [h0] using heq
      exact i.succ_ne_zero (hinj (congrArg ZMod.val hh))
    · exact hs.ne_zero h i.succ
    · exact hnonunit i.succ
  let f : Fin 5 → Fin 55 := fun i ↦ Classical.choose (htail_exists i)
  have hfval : ∀ i, nonunit105Value (f i) = (h i.succ).val := fun i ↦
    Classical.choose_spec (htail_exists i)
  have hfstrict : StrictMono f := by
    intro i j hij
    by_contra hnot
    have hji : f j ≤ f i := le_of_not_gt hnot
    have hvalji : nonunit105Value (f j) ≤ nonunit105Value (f i) :=
      nonunit105Value_strictMono.monotone hji
    have htailji : (h j.succ).val ≤ (h i.succ).val := by
      simpa only [hfval] using hvalji
    have hvij := hstrict (Fin.succ_lt_succ_iff.mpr hij)
    exact (not_lt_of_ge htailji hvij).elim
  have hf01 : (f 0).val < (f 1).val := hfstrict (by decide)
  have hf12 : (f 1).val < (f 2).val := hfstrict (by decide)
  have hf23 : (f 2).val < (f 3).val := hfstrict (by decide)
  have hf34 : (f 3).val < (f 4).val := hfstrict (by decide)
  have hf4 : (f 4).val < 55 := (f 4).isLt
  let q : IncreasingFive 55 :=
    ⟨⟨(f 0).val, by omega⟩,
      ⟨⟨(f 1).val - (f 0).val - 1, by dsimp; omega⟩,
        ⟨⟨(f 2).val - (f 1).val - 1, by dsimp; omega⟩,
          ⟨⟨(f 3).val - (f 2).val - 1, by dsimp; omega⟩,
            ⟨(f 4).val - (f 3).val - 1, by dsimp; omega⟩⟩⟩⟩⟩
  have hqindex : increasingFiveIndices q = f := by
    funext i
    fin_cases i <;> apply Fin.ext <;> simp [increasingFiveIndices, q] <;> omega
  have hq : values q = fun i ↦ (h i).val := by
    funext i
    induction i using Fin.cases with
    | zero => simp [values, hv0]
    | succ i => simp [values, hqindex, hfval]
  obtain ⟨code, hvalid, hzero⟩ := hcert q
  have hnot := relationZeroNat_not_shc (values q) code hvalid hzero
  rw [hq] at hnot
  exact hnot (by simpa only [ZMod.natCast_zmod_val] using hs)

end SHCSixExceptionalCertificate

end MinModulus
