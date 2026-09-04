/-
# The exact-Mersenne external layer-bucket table

The mixed external endpoint has two primary parameters, three possible
secondary parameters, and then two possible final parameters.  Together with
the profiles `(4,1)` and `(3,2)`, this gives 24 cases.  In every case two or
three different four-block subset layers have both the same total cardinality
and the same quotient residue.  Their combined binomial mass is larger than
the Mersenne kernel order throughout the locked range `23 <= d <= 57`.

This file records that finite arithmetic as a certificate for the general
common-bucket theorem.  The table is finite, but its output is the uniform
structural pattern used by the global endpoint, not a census of tuples.
-/
import MinModulus.G1OddPrimaryFullCyclePrimitiveExchangeMersenneLayerBuckets

namespace MinModulus

open Finset

/-- Four cardinalities selecting one subset layer from each of four disjoint
coordinate blocks. -/
structure FourLayerProfile where
  first : ℕ
  second : ℕ
  third : ℕ
  fourth : ℕ
deriving DecidableEq

def FourLayerProfile.total (P : FourLayerProfile) : ℕ :=
  P.first + P.second + P.third + P.fourth

def FourLayerProfile.weight
    (k₀ k₁ k₂ kᵣ : ℤ) (P : FourLayerProfile) : ℤ :=
  (P.first : ℤ) * k₀ + (P.second : ℤ) * k₁ +
    (P.third : ℤ) * k₂ + (P.fourth : ℤ) * kᵣ

def FourLayerProfile.mass (d t f : ℕ) (P : FourLayerProfile) : ℕ :=
  d.choose P.first * t.choose P.second *
    f.choose P.third * Nat.choose 1 P.fourth

private def bucketA (d : ℕ) : Finset FourLayerProfile :=
  let m := d / 2
  {⟨m, 2, 0, 1⟩, ⟨m, 2, 1, 0⟩}

private def bucketB (d : ℕ) : Finset FourLayerProfile :=
  let m := d / 2
  {⟨m + 1, 1, 1, 0⟩, ⟨m - 1, 2, 1, 1⟩}

private def bucketC (d : ℕ) : Finset FourLayerProfile :=
  let m := d / 2
  {⟨m, 2, 1, 0⟩, ⟨m + 1, 1, 0, 1⟩}

private def bucketD (d : ℕ) : Finset FourLayerProfile :=
  let m := d / 2
  {⟨m + 1, 2, 0, 0⟩, ⟨m - 1, 2, 1, 1⟩}

private def bucketE (d : ℕ) : Finset FourLayerProfile :=
  let m := d / 2
  {⟨m, 1, 1, 1⟩, ⟨m, 2, 1, 0⟩}

private def bucketI (d : ℕ) : Finset FourLayerProfile :=
  let m := d / 2
  {⟨m, 1, 1, 1⟩, ⟨m - 1, 2, 2, 0⟩, ⟨m + 2, 1, 0, 0⟩}

private def bucketJ (d : ℕ) : Finset FourLayerProfile :=
  let m := d / 2
  {⟨m, 1, 1, 1⟩, ⟨m, 1, 2, 0⟩, ⟨m + 1, 2, 0, 0⟩}

/-- Deterministic choice of a common layer bucket in each of the 24 allowed
parameter/profile cases.  Inputs outside those cases return the empty set. -/
def exactMersenneSelectedLayerProfiles
    (d : ℕ) (k₀ k₁ k₂ : ℤ) (t f : ℕ) : Finset FourLayerProfile :=
  if k₀ = -1 ∧ k₁ = -2 ∧ k₂ = 0 ∧ t = 4 ∧ f = 1 then bucketA d else
  if k₀ = -1 ∧ k₁ = -2 ∧ k₂ = 0 ∧ t = 3 ∧ f = 2 then bucketB d else
  if k₀ = -1 ∧ k₁ = -2 ∧ k₂ = 1 ∧ t = 4 ∧ f = 1 then bucketC d else
  if k₀ = -1 ∧ k₁ = -2 ∧ k₂ = 1 ∧ t = 3 ∧ f = 2 then bucketB d else
  if k₀ = -1 ∧ k₁ = 0 ∧ k₂ = -2 ∧ t = 4 ∧ f = 1 then bucketD d else
  if k₀ = -1 ∧ k₁ = 0 ∧ k₂ = -2 ∧ t = 3 ∧ f = 2 then bucketE d else
  if k₀ = -1 ∧ k₁ = 0 ∧ k₂ = 1 ∧ t = 4 ∧ f = 1 then bucketE d else
  if k₀ = -1 ∧ k₁ = 0 ∧ k₂ = 1 ∧ t = 3 ∧ f = 2 then bucketE d else
  if k₀ = -1 ∧ k₁ = 1 ∧ k₂ = -2 ∧ t = 4 ∧ f = 1 then bucketD d else
  if k₀ = -1 ∧ k₁ = 1 ∧ k₂ = -2 ∧ t = 3 ∧ f = 2 then bucketI d else
  if k₀ = -1 ∧ k₁ = 1 ∧ k₂ = 0 ∧ t = 4 ∧ f = 1 then bucketA d else
  if k₀ = -1 ∧ k₁ = 1 ∧ k₂ = 0 ∧ t = 3 ∧ f = 2 then bucketJ d else
  if k₀ = 0 ∧ k₁ = -2 ∧ k₂ = -1 ∧ t = 4 ∧ f = 1 then bucketA d else
  if k₀ = 0 ∧ k₁ = -2 ∧ k₂ = -1 ∧ t = 3 ∧ f = 2 then bucketJ d else
  if k₀ = 0 ∧ k₁ = -2 ∧ k₂ = 1 ∧ t = 4 ∧ f = 1 then bucketD d else
  if k₀ = 0 ∧ k₁ = -2 ∧ k₂ = 1 ∧ t = 3 ∧ f = 2 then bucketI d else
  if k₀ = 0 ∧ k₁ = -1 ∧ k₂ = -2 ∧ t = 4 ∧ f = 1 then bucketE d else
  if k₀ = 0 ∧ k₁ = -1 ∧ k₂ = -2 ∧ t = 3 ∧ f = 2 then bucketE d else
  if k₀ = 0 ∧ k₁ = -1 ∧ k₂ = 1 ∧ t = 4 ∧ f = 1 then bucketD d else
  if k₀ = 0 ∧ k₁ = -1 ∧ k₂ = 1 ∧ t = 3 ∧ f = 2 then bucketE d else
  if k₀ = 0 ∧ k₁ = 1 ∧ k₂ = -2 ∧ t = 4 ∧ f = 1 then bucketC d else
  if k₀ = 0 ∧ k₁ = 1 ∧ k₂ = -2 ∧ t = 3 ∧ f = 2 then bucketB d else
  if k₀ = 0 ∧ k₁ = 1 ∧ k₂ = -1 ∧ t = 4 ∧ f = 1 then bucketA d else
  if k₀ = 0 ∧ k₁ = 1 ∧ k₂ = -1 ∧ t = 3 ∧ f = 2 then bucketB d else
  ∅

/-- Certificate consumed by the geometric endpoint: the selected profiles
fit their four block sizes, have one total and one quotient weight, and their
combined mass exceeds the Mersenne order. -/
def MersenneExternalLayerBucketCertificate
    (d : ℕ) (k₀ k₁ k₂ : ℤ) (t f : ℕ)
    (S : Finset FourLayerProfile) : Prop :=
  0 < S.card ∧
  (∀ P : ↑S, P.1.first ≤ d) ∧
  (∀ P : ↑S, P.1.second ≤ t) ∧
  (∀ P : ↑S, P.1.third ≤ f) ∧
  (∀ P : ↑S, P.1.fourth ≤ 1) ∧
  (∀ P : ↑S, P.1.total = d / 2 + 3) ∧
  (∀ P Q : ↑S,
    P.1.weight k₀ k₁ k₂ (-1 - k₀) =
      Q.1.weight k₀ k₁ k₂ (-1 - k₀)) ∧
  2 ^ d - 1 < ∑ P ∈ S, P.mass d t f

set_option maxHeartbeats 800000 in
/-- The deterministic table is a valid common-bucket certificate in every
admissible exact-Mersenne external case. -/
theorem exactMersenneSelectedLayerProfiles_certificate
    (d : ℕ) (k₀ k₁ k₂ : ℤ) (t f : ℕ)
    (h23 : 23 ≤ d) (h57 : d ≤ 57)
    (hk₀ : k₀ = -1 ∨ k₀ = 0)
    (hk₁ : k₁ ∈ ({-2, -1, 0, 1} : Finset ℤ))
    (hk₂ : k₂ ∈ ({-2, -1, 0, 1} : Finset ℤ))
    (hk₁₀ : k₁ ≠ k₀) (hk₂₀ : k₂ ≠ k₀) (hk₂₁ : k₂ ≠ k₁)
    (hprofile : (t = 4 ∧ f = 1) ∨ (t = 3 ∧ f = 2)) :
    MersenneExternalLayerBucketCertificate d k₀ k₁ k₂ t f
      (exactMersenneSelectedLayerProfiles d k₀ k₁ k₂ t f) := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hk₁ hk₂
  rcases hk₀ with rfl | rfl <;>
    rcases hk₁ with rfl | rfl | rfl | rfl <;>
    rcases hk₂ with rfl | rfl | rfl | rfl <;>
    rcases hprofile with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  all_goals try {exfalso; omega}
  all_goals interval_cases d <;>
    (unfold MersenneExternalLayerBucketCertificate; decide)

end MinModulus
