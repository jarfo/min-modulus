/-
Computational data for six-coordinate SHC certificates. Generated proofs
import this module independently of the structural SHC development.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace MinModulus.SHCSixExceptionalCertificate

def maskSet (mask : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter fun i ↦ mask.testBit i.val

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

def maskSumNat (h : Fin 6 → ℕ) (mask : ℕ) : ℕ :=
  (if mask.testBit 0 then h 0 else 0) +
  (if mask.testBit 1 then h 1 else 0) +
  (if mask.testBit 2 then h 2 else 0) +
  (if mask.testBit 3 then h 3 else 0) +
  (if mask.testBit 4 then h 4 else 0) +
  (if mask.testBit 5 then h 5 else 0)

def relationZeroNat (h : Fin 6 → ℕ) (code : ℕ) : Bool :=
  if code < 4096 then
    decide (maskSumNat h (code % 64) % 105 = maskSumNat h (code / 64) % 105)
  else
    let data := (code - 4096) / 6
    let x : Fin 6 := ⟨(code - 4096) % 6, Nat.mod_lt _ (by norm_num)⟩
    decide ((2 * h x + maskSumNat h (data % 64)) % 105 =
      maskSumNat h (data / 64) % 105)

/-- Tail after fixing the first of five increasing indices. -/
abbrev IncreasingFiveTail (n : ℕ) (a : Fin (n - 4)) :=
  Σ b : Fin (n - a.val - 4),
    Σ c : Fin (n - (a.val + 1 + b.val) - 3),
      Σ d : Fin (n - (a.val + 1 + b.val + 1 + c.val) - 2),
        Fin (n - (a.val + 1 + b.val + 1 + c.val + 1 + d.val) - 1)

/-- Increasing selection of five indices from `Fin n`, encoded by gaps. -/
abbrev IncreasingFive (n : ℕ) := Σ a : Fin (n - 4), IncreasingFiveTail n a

def increasingFiveIndices {n : ℕ} (q : IncreasingFive n) : Fin 5 → Fin n :=
  ![⟨q.1.val, by have := q.1.isLt; omega⟩,
    ⟨q.1.val + 1 + q.2.1.val, by have := q.2.1.isLt; omega⟩,
    ⟨q.1.val + 1 + q.2.1.val + 1 + q.2.2.1.val,
      by have := q.2.2.1.isLt; omega⟩,
    ⟨q.1.val + 1 + q.2.1.val + 1 + q.2.2.1.val + 1 + q.2.2.2.1.val,
      by have := q.2.2.2.1.isLt; omega⟩,
    ⟨q.1.val + 1 + q.2.1.val + 1 + q.2.2.1.val + 1 + q.2.2.2.1.val + 1 +
      q.2.2.2.2.val, by have := q.2.2.2.2.isLt; omega⟩]

def nonunit105Value : Fin 55 → ℕ := ![
  5, 6, 7, 9, 10, 12, 14, 15, 18, 20, 21, 24, 25, 27, 28, 30, 33, 35, 36,
  39, 40, 42, 45, 48, 49, 50, 51, 54, 55, 56, 57, 60, 63, 65, 66, 69, 70,
  72, 75, 77, 78, 80, 81, 84, 85, 87, 90, 91, 93, 95, 96, 98, 99, 100, 102]

def values (q : IncreasingFive 55) : Fin 6 → ℕ :=
  Fin.cons 3 (fun i ↦ nonunit105Value (increasingFiveIndices q i))

/-- Final three increasing indices after the first two tail indices are fixed. -/
abbrev IncreasingThree (n : ℕ) :=
  Σ c : Fin (n - 2), Σ d : Fin (n - c.val - 2), Fin (n - (c.val + 1 + d.val) - 1)

def blockValues (first second : Fin 55) (q : IncreasingThree (55 - second.val - 1)) :
    Fin 6 → ℕ :=
  ![3, nonunit105Value first, nonunit105Value second,
    nonunit105Value ⟨second.val + 1 + q.1.val, by have := q.1.isLt; omega⟩,
    nonunit105Value ⟨second.val + 1 + q.1.val + 1 + q.2.1.val,
      by have := q.2.1.isLt; omega⟩,
    nonunit105Value ⟨second.val + 1 + q.1.val + 1 + q.2.1.val + 1 + q.2.2.val,
      by have := q.2.2.isLt; omega⟩]

def Certificate : Prop :=
  ∀ q : IncreasingFive 55, ∃ code,
    validRelationCode code ∧ relationZeroNat (values q) code = true

end MinModulus.SHCSixExceptionalCertificate
