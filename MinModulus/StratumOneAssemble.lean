import MinModulus.StratumOneLevels

/-!
# Assembling level vectors over a support

Given a support `T ⊆ ZMod d` and a level assignment `L : ZMod d → ℕ`, the
assembled vector is `∑_{t ∈ T} rep(t, L t)`.  Two facts drive the
stratum-one triple:

* its **value** is `∑_{t ∈ T} 2^(t-1)`, *independent of the levels*;
* its **coordinate sum** is `|T| - ∑_{t ∈ T} L t`.

So any level assignment with `∑ L = |T| - 1` produces a vector of
coordinate sum `1` and the prescribed value — a rival in the stratum-one
sense.  The triple then only has to choose two such assignments whose sum
is bounded by `1` coordinatewise.
-/

namespace MinModulus

open Finset

namespace StratumOne

variable {d : ℕ} [NeZero d]

/-- The vector assembled from a level assignment over a support. -/
def assemble (T : Finset (ZMod d)) (L : ZMod d → ℕ) : ZMod d → ℤ :=
  fun x => ∑ t ∈ T, levelVec t (L t) x

/-- The coordinate sum of an assembled vector is `|T| - ∑ L`. -/
theorem coeffSum_assemble (T : Finset (ZMod d)) (L : ZMod d → ℕ)
    (hL : ∀ t ∈ T, L t ≤ d) :
    coeffSum (assemble T L) = (T.card : ℤ) - ∑ t ∈ T, (L t : ℤ) := by
  classical
  unfold coeffSum assemble
  rw [Finset.sum_comm]
  have hinner : ∀ t ∈ T, (∑ x, levelVec t (L t) x) = 1 - (L t : ℤ) := by
    intro t ht
    have h := coeffSum_levelVec t (hL t ht)
    unfold coeffSum at h
    exact h
  rw [Finset.sum_congr rfl hinner, Finset.sum_sub_distrib]
  simp

/-- The value of an assembled vector is `∑_{t ∈ T} 2^(t-1)`, whatever the
levels are.  This is the telescoping that makes the construction work. -/
theorem value_assemble (T : Finset (ZMod d)) (L : ZMod d → ℕ)
    (hL : ∀ t ∈ T, L t ≤ d) :
    value (assemble T L) = ∑ t ∈ T, pow2 (t - 1) := by
  classical
  unfold value assemble
  have hstep : ∀ x : ZMod d,
      (∑ t ∈ T, levelVec t (L t) x) • pow2 x
        = ∑ t ∈ T, (levelVec t (L t) x) • pow2 x := by
    intro x; rw [Finset.sum_smul]
  rw [Finset.sum_congr rfl (fun x _ => hstep x), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  have h := value_levelVec t (hL t ht)
  unfold value at h
  exact h

end StratumOne

end MinModulus
