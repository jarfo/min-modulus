/-
# Kernel-checked normalized six-coordinate certificates

This file provides the trusted interface for normalized six-coordinate
exclusions.  A certificate gives, for every increasing tuple
`1 < a < b < c < d < e < N`, either a subset-sum collision or a forbidden
single-head-2 relation.  Generated files prove only modular natural-number
equalities; the lemmas below translate them into the corresponding SHC
clauses.
-/
import MinModulus.SHCSixGeneratorComplete
import Mathlib.Data.Fin.Tuple.Sort

namespace MinModulus

open Finset

namespace SHCSixCertificate

set_option maxRecDepth 100000

/-- The subset of six coordinates encoded by the low six bits of `mask`. -/
def maskSet (mask : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter fun i ↦ mask.testBit i.val

/-- Direct six-term subset sum, optimized for kernel reduction. -/
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

/-- Relation-code validity.  Codes below 4096 encode two distinct subset
sums.  Larger codes encode a head, positive set, and negative set satisfying
the hypotheses of the SHC head-2 clause. -/
def validRelationCode (code : ℕ) : Prop :=
  if code < 4096 then
    maskSet (code % 64) ≠ maskSet (code / 64)
  else
    let data := (code - 4096) / 6
    let x : Fin 6 := ⟨(code - 4096) % 6, Nat.mod_lt _ (by norm_num)⟩
    let P := maskSet (data % 64)
    let M := maskSet (data / 64)
    x ∉ P ∧ x ∉ M ∧ Disjoint P M ∧ P.card + 1 ≤ M.card

instance (code : ℕ) : Decidable (validRelationCode code) := by
  unfold validRelationCode
  infer_instance

/-- Direct natural-number subset sum used by generated computations. -/
def maskSumNat (h : Fin 6 → ℕ) (mask : ℕ) : ℕ :=
  (if mask.testBit 0 then h 0 else 0) +
  (if mask.testBit 1 then h 1 else 0) +
  (if mask.testBit 2 then h 2 else 0) +
  (if mask.testBit 3 then h 3 else 0) +
  (if mask.testBit 4 then h 4 else 0) +
  (if mask.testBit 5 then h 5 else 0)

/-- The modular equality asserted by a relation code. -/
def relationZeroNat (N : ℕ) (h : Fin 6 → ℕ) (code : ℕ) : Bool :=
  if code < 4096 then
    decide (maskSumNat h (code % 64) % N = maskSumNat h (code / 64) % N)
  else
    let data := (code - 4096) / 6
    let x : Fin 6 := ⟨(code - 4096) % 6, Nat.mod_lt _ (by norm_num)⟩
    decide ((2 * h x + maskSumNat h (data % 64)) % N =
      maskSumNat h (data / 64) % N)

/-- A list covers a tuple when one encoded modular relation holds. -/
def coveredNat (N : ℕ) (codes : List ℕ) (h : Fin 6 → ℕ) : Bool :=
  codes.any fun code ↦ relationZeroNat N h code

theorem coveredNat_exists_valid (N : ℕ) (codes : List ℕ) (h : Fin 6 → ℕ)
    (hvalid : ∀ code ∈ codes, validRelationCode code)
    (hc : coveredNat N codes h = true) : ∃ code,
      validRelationCode code ∧ relationZeroNat N h code = true := by
  simp only [coveredNat, List.any_eq_true] at hc
  obtain ⟨code, hmem, hzero⟩ := hc
  exact ⟨code, hvalid code hmem, hzero⟩

theorem natCast_maskSumNat {N : ℕ} [NeZero N] (h : Fin 6 → ℕ) (mask : ℕ) :
    ((maskSumNat h mask : ℕ) : ZMod N) =
      maskSum (fun i ↦ (h i : ZMod N)) mask := by
  simp [maskSumNat, maskSum]

/-- A valid relation code whose modular equality holds contradicts SHC. -/
theorem relationZeroNat_not_shc {N : ℕ} [NeZero N] (h : Fin 6 → ℕ) (code : ℕ)
    (hvalid : validRelationCode code) (hzero : relationZeroNat N h code = true) :
    ¬ SHC (fun i ↦ (h i : ZMod N)) := by
  intro hs
  unfold validRelationCode at hvalid
  unfold relationZeroNat at hzero
  split at hvalid <;> split at hzero
  · simp only [decide_eq_true_eq] at hzero
    have heq : maskSum (fun i ↦ (h i : ZMod N)) (code % 64) =
        maskSum (fun i ↦ (h i : ZMod N)) (code / 64) := by
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
          maskSumNat h (((code - 4096) / 6) % 64) : ℕ) : ZMod N) =
          (maskSumNat h (((code - 4096) / 6) / 64) : ZMod N) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact hzero
    have heq :
        2 • ((h ⟨(code - 4096) % 6, Nat.mod_lt _ (by norm_num)⟩ : ℕ) : ZMod N) +
          maskSum (fun i ↦ (h i : ZMod N)) (((code - 4096) / 6) % 64) =
          maskSum (fun i ↦ (h i : ZMod N)) (((code - 4096) / 6) / 64) := by
      rw [← natCast_maskSumNat, ← natCast_maskSumNat]
      simpa [Nat.cast_add, Nat.cast_mul, nsmul_eq_mul] using heqcast
    rw [maskSum_eq_sum, maskSum_eq_sum] at heq
    exact hs.sh2 _ _ _ hvalid.1 hvalid.2.1 hvalid.2.2.1 hvalid.2.2.2 heq

/-- Tail after fixing the first of five increasing values chosen after `1`. -/
abbrev IncreasingFiveTail (n : ℕ) (a : Fin (n - 4)) :=
  Σ b : Fin (n - a.val - 4),
    Σ c : Fin (n - (a.val + 1 + b.val) - 3),
      Σ d : Fin (n - (a.val + 1 + b.val + 1 + c.val) - 2),
        Fin (n - (a.val + 1 + b.val + 1 + c.val + 1 + d.val) - 1)

/-- Increasing selection of five values from `2, ..., N - 1`, encoded by gaps. -/
abbrev IncreasingFive (n : ℕ) := Σ a : Fin (n - 4), IncreasingFiveTail n a

/-- The normalized six-tuple represented by five gap coordinates. -/
def increasingFiveValues {N : ℕ} (q : IncreasingFive (N - 2)) : Fin 6 → ℕ :=
  ![1,
    q.1.val + 2,
    q.1.val + q.2.1.val + 3,
    q.1.val + q.2.1.val + q.2.2.1.val + 4,
    q.1.val + q.2.1.val + q.2.2.1.val + q.2.2.2.1.val + 5,
    q.1.val + q.2.1.val + q.2.2.1.val + q.2.2.2.1.val + q.2.2.2.2.val + 6]

/-- Final three gap coordinates after the first three values are fixed. -/
abbrev IncreasingThree (n : ℕ) :=
  Σ c : Fin (n - 2), Σ d : Fin (n - c.val - 2), Fin (n - (c.val + 1 + d.val) - 1)

def blockValues (a b : ℕ) {n : ℕ} (q : IncreasingThree n) : Fin 6 → ℕ :=
  ![1, a, b, b + 1 + q.1.val, b + 2 + q.1.val + q.2.1.val,
    b + 3 + q.1.val + q.2.1.val + q.2.2.val]

/-- A finite certificate covering every normalized increasing six-tuple. -/
def Certificate (N : ℕ) : Prop :=
  ∀ q : IncreasingFive (N - 2), ∃ code,
    validRelationCode code ∧ relationZeroNat N (increasingFiveValues q) code = true

/-- Sorted form of the normalized six-coordinate exclusion. -/
def SortedNormalizedSHCSixExcluded (N : ℕ) : Prop :=
  ∀ h : Fin 6 → ZMod N, h 0 = 1 → Monotone (fun i ↦ (h i).val) → ¬ SHC h

/-- Sorting canonical representatives preserves the normalized coordinate. -/
theorem normalizedSHCSixExcluded_of_sorted {N : ℕ} (hN : 2 ≤ N)
    (hsorted : SortedNormalizedSHCSixExcluded N) : NormalizedSHCExcluded 5 N := by
  letI : NeZero N := ⟨by omega⟩
  letI : Fact (1 < N) := ⟨hN⟩
  intro h h0 hs
  let p : Fin 6 ≃ Fin 6 := Tuple.sort (fun i ↦ (h i).val)
  let h' : Fin 6 → ZMod N := h ∘ p
  have hsh' : SHC h' := hs.reindex_equiv h p
  have hmono : Monotone (fun i ↦ (h' i).val) :=
    Tuple.monotone_sort (fun i ↦ (h i).val)
  have h'0 : h' 0 = 1 := by
    let j : Fin 6 := p.symm 0
    have hj : h' j = 1 := by
      simp [h', j, p, h0]
    have hle : (h' 0).val ≤ 1 := by
      have := hmono (Fin.zero_le j)
      simpa [hj, ZMod.val_one] using this
    have hpos : 0 < (h' 0).val := ZMod.val_pos.mpr (hsh'.ne_zero h' 0)
    apply ZMod.val_injective
    simpa [ZMod.val_one] using (show (h' 0).val = 1 by omega)
  exact hsorted h' h'0 hmono hsh'

/-- Convert a certificate over gap coordinates into the sorted exclusion. -/
theorem sortedNormalizedSHCSixExcluded_of_certificate {N : ℕ} (hN : 6 ≤ N)
    (hcert : Certificate N) : SortedNormalizedSHCSixExcluded N := by
  letI : NeZero N := ⟨by omega⟩
  letI : Fact (1 < N) := ⟨by omega⟩
  intro h h0 hmono hs
  have hinj : Function.Injective (fun i ↦ (h i).val) := by
    intro i j hij
    have hh : h i = h j := by
      apply ZMod.val_injective
      exact hij
    have hsum : (∑ k ∈ ({i} : Finset (Fin 6)), h k) =
        ∑ k ∈ ({j} : Finset (Fin 6)), h k := by simp [hh]
    exact Finset.singleton_injective (hs.dis hsum)
  have hstrict : StrictMono (fun i ↦ (h i).val) := hmono.strictMono_of_injective hinj
  have hv0 : (h 0).val = 1 := by rw [h0]; exact ZMod.val_one N
  have h01 : (h 0).val < (h 1).val := hstrict (by decide)
  have h12 : (h 1).val < (h 2).val := hstrict (by decide)
  have h23 : (h 2).val < (h 3).val := hstrict (by decide)
  have h34 : (h 3).val < (h 4).val := hstrict (by decide)
  have h45 : (h 4).val < (h 5).val := hstrict (by decide)
  have hv1 : (h 1).val < N := (h 1).val_lt
  have hv2 : (h 2).val < N := (h 2).val_lt
  have hv3 : (h 3).val < N := (h 3).val_lt
  have hv4 : (h 4).val < N := (h 4).val_lt
  have hv5 : (h 5).val < N := (h 5).val_lt
  let q : IncreasingFive (N - 2) :=
    ⟨⟨(h 1).val - 2, by omega⟩,
      ⟨⟨(h 2).val - (h 1).val - 1, by dsimp; omega⟩,
        ⟨⟨(h 3).val - (h 2).val - 1, by dsimp; omega⟩,
          ⟨⟨(h 4).val - (h 3).val - 1, by dsimp; omega⟩,
            ⟨(h 5).val - (h 4).val - 1, by dsimp; omega⟩⟩⟩⟩⟩
  have hq : increasingFiveValues q = fun i ↦ (h i).val := by
    funext i
    fin_cases i <;> simp [increasingFiveValues, q] <;> omega
  obtain ⟨code, hvalid, hzero⟩ := hcert q
  have hnot := relationZeroNat_not_shc (increasingFiveValues q) code hvalid hzero
  rw [hq] at hnot
  exact hnot (by simpa only [ZMod.natCast_zmod_val] using hs)

/-- A kernel-checked certificate proves the unrestricted normalized target. -/
theorem normalizedSHCSixExcluded_of_certificate {N : ℕ} (hN : 6 ≤ N)
    (hcert : Certificate N) : NormalizedSHCExcluded 5 N :=
  normalizedSHCSixExcluded_of_sorted (by omega)
    (sortedNormalizedSHCSixExcluded_of_certificate hN hcert)

end SHCSixCertificate

/-- The first six-coordinate window case follows directly from the bottom wedge. -/
theorem normalized_shc_six_excluded_sixty_five : NormalizedSHCExcluded 5 65 := by
  intro h h0 hs
  have hw := bottom_wedge h (add_self_injective_zmod (by norm_num : Odd 65))
    hs.dis hs.sh2 hs.sh3
  norm_num [ZMod.card] at hw

end MinModulus
