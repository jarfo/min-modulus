/-
# Kernel-checked normalized five-coordinate certificates

This file provides the small trusted interface used by generated normalized
five-coordinate exclusions.  A certificate gives, for every increasing tuple
`1 < a < b < c < d < N`, either a subset-sum collision or a forbidden
single-head-2 relation.  The computational files prove only modular natural
number equalities; the lemmas below translate them to the corresponding SHC
clauses.

The first window modulus, 33, needs no certificate: the bottom-wedge theorem
already excludes a five-coordinate SHC family there.
-/
import MinModulus.SHCFiveGenerator
import Mathlib.Data.Fin.Tuple.Sort

namespace MinModulus

open Finset

namespace SHCFiveCertificate

/-- The subset of five coordinates encoded by the low five bits of `mask`. -/
def maskSet (mask : ℕ) : Finset (Fin 5) :=
  Finset.univ.filter fun i ↦ mask.testBit i.val

/-- Direct five-term subset sum, optimized for kernel reduction. -/
def maskSum {G : Type*} [AddCommMonoid G] (h : Fin 5 → G) (mask : ℕ) : G :=
  (if mask.testBit 0 then h 0 else 0) +
  (if mask.testBit 1 then h 1 else 0) +
  (if mask.testBit 2 then h 2 else 0) +
  (if mask.testBit 3 then h 3 else 0) +
  (if mask.testBit 4 then h 4 else 0)

theorem maskSum_eq_sum {G : Type*} [AddCommMonoid G]
    (h : Fin 5 → G) (mask : ℕ) :
    maskSum h mask = ∑ i ∈ maskSet mask, h i := by
  simp only [maskSet, Finset.sum_filter]
  rw [Fin.sum_univ_five]
  simp [maskSum]
  rfl

/-- Relation-code validity.  Codes below 1024 encode two distinct subset
sums.  Larger codes encode a head, positive set, and negative set satisfying
the hypotheses of the SHC head-2 clause. -/
def validRelationCode (code : ℕ) : Prop :=
  if code < 1024 then
    maskSet (code % 32) ≠ maskSet (code / 32)
  else
    let data := (code - 1024) / 5
    let x : Fin 5 := ⟨(code - 1024) % 5, Nat.mod_lt _ (by norm_num)⟩
    let P := maskSet (data % 32)
    let M := maskSet (data / 32)
    x ∉ P ∧ x ∉ M ∧ Disjoint P M ∧ P.card + 1 ≤ M.card

instance (code : ℕ) : Decidable (validRelationCode code) := by
  unfold validRelationCode
  infer_instance

/-- Direct natural-number subset sum used by generated computations. -/
def maskSumNat (h : Fin 5 → ℕ) (mask : ℕ) : ℕ :=
  (if mask.testBit 0 then h 0 else 0) +
  (if mask.testBit 1 then h 1 else 0) +
  (if mask.testBit 2 then h 2 else 0) +
  (if mask.testBit 3 then h 3 else 0) +
  (if mask.testBit 4 then h 4 else 0)

/-- The modular equality asserted by a relation code. -/
def relationZeroNat (N : ℕ) (h : Fin 5 → ℕ) (code : ℕ) : Bool :=
  if code < 1024 then
    decide (maskSumNat h (code % 32) % N = maskSumNat h (code / 32) % N)
  else
    let data := (code - 1024) / 5
    let x : Fin 5 := ⟨(code - 1024) % 5, Nat.mod_lt _ (by norm_num)⟩
    decide ((2 * h x + maskSumNat h (data % 32)) % N =
      maskSumNat h (data / 32) % N)

/-- A list covers a tuple when one encoded modular relation holds. -/
def coveredNat (N : ℕ) (codes : List ℕ) (h : Fin 5 → ℕ) : Bool :=
  codes.any fun code ↦ relationZeroNat N h code

theorem coveredNat_exists_valid (N : ℕ) (codes : List ℕ) (h : Fin 5 → ℕ)
    (hvalid : ∀ code ∈ codes, validRelationCode code)
    (hc : coveredNat N codes h = true) : ∃ code,
      validRelationCode code ∧ relationZeroNat N h code = true := by
  simp only [coveredNat, List.any_eq_true] at hc
  obtain ⟨code, hmem, hzero⟩ := hc
  exact ⟨code, hvalid code hmem, hzero⟩

theorem natCast_maskSumNat {N : ℕ} [NeZero N] (h : Fin 5 → ℕ) (mask : ℕ) :
    ((maskSumNat h mask : ℕ) : ZMod N) = maskSum (fun i ↦ (h i : ZMod N)) mask := by
  simp [maskSumNat, maskSum]

/-- A valid relation code whose modular equality holds contradicts SHC. -/
theorem relationZeroNat_not_shc {N : ℕ} [NeZero N] (h : Fin 5 → ℕ) (code : ℕ)
    (hvalid : validRelationCode code) (hzero : relationZeroNat N h code = true) :
    ¬ SHC (fun i ↦ (h i : ZMod N)) := by
  intro hs
  unfold validRelationCode at hvalid
  unfold relationZeroNat at hzero
  split at hvalid <;> split at hzero
  · simp only [decide_eq_true_eq] at hzero
    have heq : maskSum (fun i ↦ (h i : ZMod N)) (code % 32) =
        maskSum (fun i ↦ (h i : ZMod N)) (code / 32) := by
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
        ((2 * h ⟨(code - 1024) % 5, Nat.mod_lt _ (by norm_num)⟩ +
          maskSumNat h (((code - 1024) / 5) % 32) : ℕ) : ZMod N) =
          (maskSumNat h (((code - 1024) / 5) / 32) : ZMod N) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact hzero
    have heq : 2 • ((h ⟨(code - 1024) % 5, Nat.mod_lt _ (by norm_num)⟩ : ℕ) : ZMod N) +
          maskSum (fun i ↦ (h i : ZMod N)) (((code - 1024) / 5) % 32) =
          maskSum (fun i ↦ (h i : ZMod N)) (((code - 1024) / 5) / 32) := by
      rw [← natCast_maskSumNat, ← natCast_maskSumNat]
      simpa [Nat.cast_add, Nat.cast_mul, nsmul_eq_mul] using heqcast
    rw [maskSum_eq_sum, maskSum_eq_sum] at heq
    exact hs.sh2 _ _ _ hvalid.1 hvalid.2.1 hvalid.2.2.1 hvalid.2.2.2 heq

/-- Gap coordinates for four strictly increasing values chosen after `1`. -/
abbrev IncreasingFourTail (n : ℕ) (a : Fin (n - 3)) :=
  Σ b : Fin (n - a.val - 3),
    Σ c : Fin (n - (a.val + 1 + b.val) - 2),
      Fin (n - (a.val + 1 + b.val + 1 + c.val) - 1)

abbrev IncreasingFour (n : ℕ) :=
  Σ a : Fin (n - 3), IncreasingFourTail n a

/-- The actual tuple represented by four gap coordinates. -/
def increasingFourValues {N : ℕ} (q : IncreasingFour (N - 2)) : Fin 5 → ℕ :=
  ![1,
    q.1.val + 2,
    q.1.val + q.2.1.val + 3,
    q.1.val + q.2.1.val + q.2.2.1.val + 4,
    q.1.val + q.2.1.val + q.2.2.1.val + q.2.2.2.val + 5]

/-- The final two gap coordinates after the first three values are fixed. -/
abbrev IncreasingTwo (n : ℕ) :=
  Σ c : Fin (n - 1), Fin (n - c.val - 1)

def blockValues (a b : ℕ) {n : ℕ} (q : IncreasingTwo n) : Fin 5 → ℕ :=
  ![1, a, b, b + 1 + q.1.val, b + 2 + q.1.val + q.2.val]

/-- A finite certificate covering every normalized increasing five-tuple. -/
def Certificate (N : ℕ) : Prop :=
  ∀ q : IncreasingFour (N - 2), ∃ code,
    validRelationCode code ∧ relationZeroNat N (increasingFourValues q) code = true

/-- Sorted form of the normalized five-coordinate exclusion. -/
def SortedNormalizedSHCFiveExcluded (N : ℕ) : Prop :=
  ∀ h : Fin 5 → ZMod N, h 0 = 1 → Monotone (fun i ↦ (h i).val) → ¬ SHC h

/-- Sorting canonical representatives preserves the normalized coordinate. -/
theorem normalizedSHCFiveExcluded_of_sorted {N : ℕ} (hN : 2 ≤ N)
    (hsorted : SortedNormalizedSHCFiveExcluded N) : NormalizedSHCExcluded 4 N := by
  letI : NeZero N := ⟨by omega⟩
  letI : Fact (1 < N) := ⟨hN⟩
  intro h h0 hs
  let p : Fin 5 ≃ Fin 5 := Tuple.sort (fun i ↦ (h i).val)
  let h' : Fin 5 → ZMod N := h ∘ p
  have hsh' : SHC h' := hs.reindex_equiv h p
  have hmono : Monotone (fun i ↦ (h' i).val) := by
    exact Tuple.monotone_sort (fun i ↦ (h i).val)
  have h'0 : h' 0 = 1 := by
    let j : Fin 5 := p.symm 0
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
theorem sortedNormalizedSHCFiveExcluded_of_certificate {N : ℕ} (hN : 5 ≤ N)
    (hcert : Certificate N) : SortedNormalizedSHCFiveExcluded N := by
  letI : NeZero N := ⟨by omega⟩
  letI : Fact (1 < N) := ⟨by omega⟩
  intro h h0 hmono hs
  have hinj : Function.Injective (fun i ↦ (h i).val) := by
    intro i j hij
    have hh : h i = h j := by
      apply ZMod.val_injective
      exact hij
    have hsum : (∑ k ∈ ({i} : Finset (Fin 5)), h k) =
        ∑ k ∈ ({j} : Finset (Fin 5)), h k := by simp [hh]
    exact Finset.singleton_injective (hs.dis hsum)
  have hstrict : StrictMono (fun i ↦ (h i).val) := hmono.strictMono_of_injective hinj
  have hv0 : (h 0).val = 1 := by rw [h0]; exact ZMod.val_one N
  have h01 : (h 0).val < (h 1).val :=
    hstrict (show (0 : Fin 5) < 1 by decide)
  have h12 : (h 1).val < (h 2).val :=
    hstrict (show (1 : Fin 5) < 2 by decide)
  have h23 : (h 2).val < (h 3).val :=
    hstrict (show (2 : Fin 5) < 3 by decide)
  have h34 : (h 3).val < (h 4).val :=
    hstrict (show (3 : Fin 5) < 4 by decide)
  have hv1 : (h 1).val < N := (h 1).val_lt
  have hv2 : (h 2).val < N := (h 2).val_lt
  have hv3 : (h 3).val < N := (h 3).val_lt
  have hv4 : (h 4).val < N := (h 4).val_lt
  let q : IncreasingFour (N - 2) :=
    ⟨⟨(h 1).val - 2, by omega⟩,
      ⟨⟨(h 2).val - (h 1).val - 1, by dsimp; omega⟩,
        ⟨⟨(h 3).val - (h 2).val - 1, by dsimp; omega⟩,
          ⟨(h 4).val - (h 3).val - 1, by dsimp; omega⟩⟩⟩⟩
  have hq : increasingFourValues q = fun i ↦ (h i).val := by
    funext i
    fin_cases i <;> simp [increasingFourValues, q] <;> omega
  obtain ⟨code, hvalid, hzero⟩ := hcert q
  have hnot := relationZeroNat_not_shc (increasingFourValues q) code hvalid hzero
  rw [hq] at hnot
  exact hnot (by simpa only [ZMod.natCast_zmod_val] using hs)

/-- A kernel-checked certificate proves the unrestricted normalized target. -/
theorem normalizedSHCFiveExcluded_of_certificate {N : ℕ} (hN : 5 ≤ N)
    (hcert : Certificate N) : NormalizedSHCExcluded 4 N :=
  normalizedSHCFiveExcluded_of_sorted (by omega)
    (sortedNormalizedSHCFiveExcluded_of_certificate hN hcert)

end SHCFiveCertificate

/-- The first five-coordinate window case follows directly from the bottom wedge. -/
theorem normalized_shc_five_excluded_thirty_three : NormalizedSHCExcluded 4 33 := by
  intro h h0 hs
  have hw := bottom_wedge h (add_self_injective_zmod (by norm_num : Odd 33))
    hs.dis hs.sh2 hs.sh3
  norm_num [ZMod.card] at hw

end MinModulus
