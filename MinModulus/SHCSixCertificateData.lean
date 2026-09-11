/-
Computational data for six-coordinate SHC certificates. Generated proofs
import this module independently of the structural SHC development.
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

namespace MinModulus.SHCSixCertificate

/-- The subset of six coordinates encoded by the low six bits of `mask`. -/
def maskSet (mask : ℕ) : Finset (Fin 6) :=
  Finset.univ.filter fun i ↦ mask.testBit i.val

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

end MinModulus.SHCSixCertificate
