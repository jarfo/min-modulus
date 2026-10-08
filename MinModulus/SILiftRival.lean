import MinModulus.SILiftSheet
import MinModulus.SILiftShift

/-!
# The rival criterion

A parent whose deletion-child is the exact SI block consists of chosen base
lifts `A i` adjusted by sheet bits `b i`, together with an extra entry `e`.
A rival is a coin family `κ` that avoids the extra coordinate and still
reproduces the total.

Expanding `∑ κ i • G i = ∑ G i` over that decomposition splits the
condition into two independent parts, because the sheet is its own
negative:

* a **base equation**, in the sum of the `A i` weighted by `κ`, and
* a **sheet condition**, which depends only on `∑ κ i * b i` modulo two.

`sheetSum_weighted` is the combinatorial half of the bridge: it identifies
that parity with `sheetSum`, the sum of the sheet bits over the exponents
of EVEN multiplicity.  The even multiplicities are the right ones because
the rival is compared against the all-ones family, and `κ i - 1` is odd
exactly when `κ i` is even.
-/

namespace MinModulus

open Finset

section Rival

variable {m t : ℕ}

/-- A parent over the exact SI child: base lifts adjusted by sheet bits,
with the extra entry last. -/
def siLiftParent (m t : ℕ) (A : Fin (m + 1) → ZMod (siFull m t)) (b : ℕ → ℕ)
    (e : ZMod (siFull m t)) : Fin (m + 2) → ZMod (siFull m t) :=
  Fin.snoc (fun i : Fin (m + 1) => A i + (b i.val) • siSheet m t) e

@[simp] lemma siLiftParent_castSucc (A : Fin (m + 1) → ZMod (siFull m t))
    (b : ℕ → ℕ) (e : ZMod (siFull m t)) (i : Fin (m + 1)) :
    siLiftParent m t A b e i.castSucc = A i + (b i.val) • siSheet m t := by
  simp [siLiftParent]

@[simp] lemma siLiftParent_last (A : Fin (m + 1) → ZMod (siFull m t))
    (b : ℕ → ℕ) (e : ZMod (siFull m t)) :
    siLiftParent m t A b e (Fin.last (m + 1)) = e := by
  simp [siLiftParent]

/-- The total of the parent splits into base, sheet and extra. -/
lemma siLiftParent_sum (A : Fin (m + 1) → ZMod (siFull m t)) (b : ℕ → ℕ)
    (e : ZMod (siFull m t)) :
    ∑ i, siLiftParent m t A b e i
      = (∑ i : Fin (m + 1), A i)
        + (∑ i : Fin (m + 1), b i.val) • siSheet m t + e := by
  rw [Fin.sum_univ_castSucc]
  simp only [siLiftParent_castSucc, siLiftParent_last]
  rw [Finset.sum_add_distrib, ← Finset.sum_smul]

/-- The weighted total of a family avoiding the extra coordinate. -/
lemma siLiftParent_weighted_sum (A : Fin (m + 1) → ZMod (siFull m t))
    (b : ℕ → ℕ) (e : ZMod (siFull m t)) (κ : Fin (m + 2) → ℕ)
    (hκ : κ (Fin.last (m + 1)) = 0) :
    ∑ i, κ i • siLiftParent m t A b e i
      = (∑ i : Fin (m + 1), κ i.castSucc • A i)
        + (∑ i : Fin (m + 1), κ i.castSucc * b i.val) • siSheet m t := by
  rw [Fin.sum_univ_castSucc]
  simp only [siLiftParent_castSucc, siLiftParent_last, hκ, zero_smul, add_zero]
  have h : ∀ i : Fin (m + 1),
      κ i.castSucc • (A i + (b i.val) • siSheet m t)
        = κ i.castSucc • A i + (κ i.castSucc * b i.val) • siSheet m t := by
    intro i
    rw [smul_add, smul_smul]
  rw [Finset.sum_congr rfl (fun i _ => h i), Finset.sum_add_distrib,
    ← Finset.sum_smul]

/-- **The rival criterion.**  A family avoiding the extra coordinate
reproduces the total exactly when the base sums agree after the sheet terms
are collapsed to their parities. -/
theorem siLiftParent_rival_iff (A : Fin (m + 1) → ZMod (siFull m t))
    (b : ℕ → ℕ) (e : ZMod (siFull m t)) (κ : Fin (m + 2) → ℕ)
    (hκ : κ (Fin.last (m + 1)) = 0) :
    (∑ i, κ i • siLiftParent m t A b e i = ∑ i, siLiftParent m t A b e i)
      ↔ (∑ i : Fin (m + 1), κ i.castSucc • A i)
          + (∑ i : Fin (m + 1), κ i.castSucc * b i.val) • siSheet m t
        = (∑ i : Fin (m + 1), A i)
          + (∑ i : Fin (m + 1), b i.val) • siSheet m t + e := by
  rw [siLiftParent_weighted_sum A b e κ hκ, siLiftParent_sum A b e]

/-! ### The combinatorial half of the bridge -/

/-- **Sheet parity is `sheetSum`.**  The parity of `∑ κ i * b i + ∑ b i` —
which is what the sheet terms of the rival criterion compare — is exactly
the parity of the sheet bits over the exponents of EVEN multiplicity. -/
theorem sheetSum_weighted (w : ℕ) (b κ : ℕ → ℕ) :
    (∑ i ∈ range w, κ i * b i + ∑ i ∈ range w, b i) % 2
      = sheetSum w b κ % 2 := by
  classical
  have hterm : ∀ i, ((κ i + 1) * b i) % 2
      = (if κ i % 2 = 0 then b i else 0) % 2 := by
    intro i
    rcases Nat.even_or_odd (κ i) with he | ho
    · obtain ⟨c, hc⟩ := he
      rw [if_pos (by omega), hc,
        show (c + c + 1) * b i = 2 * (c * b i) + b i from by ring]
      omega
    · obtain ⟨c, hc⟩ := ho
      rw [if_neg (by omega), hc,
        show (2 * c + 1 + 1) * b i = 2 * ((c + 1) * b i) from by ring]
      omega
  calc (∑ i ∈ range w, κ i * b i + ∑ i ∈ range w, b i) % 2
      = (∑ i ∈ range w, (κ i + 1) * b i) % 2 := by
        rw [← Finset.sum_add_distrib]
        exact congrArg (· % 2) (Finset.sum_congr rfl fun i _ => by ring)
    _ = (∑ i ∈ range w, ((κ i + 1) * b i) % 2) % 2 := Finset.sum_nat_mod _ _ _
    _ = (∑ i ∈ range w, (if κ i % 2 = 0 then b i else 0) % 2) % 2 := by
        exact congrArg (· % 2) (Finset.sum_congr rfl fun i _ => hterm i)
    _ = sheetSum w b κ % 2 := (Finset.sum_nat_mod _ _ _).symm

/-- The sheet contribution of a rival, written through `sheetSum`. -/
theorem siLiftParent_sheet_term (hm : t ≤ m) (b κ : ℕ → ℕ) :
    (∑ i ∈ range (m + 1), κ i * b i) • siSheet m t
      + (∑ i ∈ range (m + 1), b i) • siSheet m t
      = (sheetSum (m + 1) b κ) • siSheet m t := by
  rw [← add_smul]
  exact nsmul_siSheet_congr hm (sheetSum_weighted (m + 1) b κ)

/-- Every multiple of the sheet is its own negative. -/
lemma neg_nsmul_siSheet (hm : t ≤ m) (c : ℕ) :
    -(c • siSheet m t) = c • siSheet m t := by
  have h : c • siSheet m t + c • siSheet m t = 0 := by
    rw [← add_smul, nsmul_siSheet hm (c + c),
      show (c + c) % 2 = 0 from by omega, zero_smul]
  exact neg_eq_of_add_eq_zero_left h

/-- **The rival criterion with the sheet collapsed to `sheetSum`.**  This is
the form the parity machinery consumes: the base equation is shifted by the
sheet exactly when the sheet bits over the EVEN-multiplicity exponents sum
to an odd number. -/
theorem siLiftParent_rival_sheetSum (hm : t ≤ m)
    (A : Fin (m + 1) → ZMod (siFull m t)) (b : ℕ → ℕ)
    (e : ZMod (siFull m t)) (κ : Fin (m + 2) → ℕ) (κ₀ : ℕ → ℕ)
    (hκ : κ (Fin.last (m + 1)) = 0)
    (hagree : ∀ i : Fin (m + 1), κ i.castSucc = κ₀ i.val)
    (hrival : ∑ i, κ i • siLiftParent m t A b e i
      = ∑ i, siLiftParent m t A b e i) :
    (∑ i : Fin (m + 1), κ i.castSucc • A i)
      = (∑ i : Fin (m + 1), A i) + e
        + (sheetSum (m + 1) b κ₀) • siSheet m t := by
  rw [siLiftParent_rival_iff A b e κ hκ] at hrival
  -- rewrite both sheet coefficients as sums over `range (m+1)`
  have h1 : (∑ i : Fin (m + 1), κ i.castSucc * b i.val)
      = ∑ j ∈ range (m + 1), κ₀ j * b j := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => κ₀ j * b j) (m + 1)]
    exact Finset.sum_congr rfl fun i _ => by rw [hagree i]
  have h2 : (∑ i : Fin (m + 1), b i.val) = ∑ j ∈ range (m + 1), b j :=
    Fin.sum_univ_eq_sum_range b (m + 1)
  rw [h1, h2] at hrival
  -- move the rival's own sheet term across; it is its own negative
  -- move the rival's own sheet term across; it is its own negative
  have hmove := congrArg
    (fun z => z - (∑ j ∈ range (m + 1), κ₀ j * b j) • siSheet m t) hrival
  simp only [add_sub_cancel_right] at hmove
  rw [hmove, sub_eq_add_neg, neg_nsmul_siSheet hm,
    ← siLiftParent_sheet_term hm b κ₀]
  abel

end Rival

end MinModulus
