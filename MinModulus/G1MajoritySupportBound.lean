/-
# Critical weight floor bounds the majority support

Strict majority is useful only after comparison with the certified lower
bound on total canonical padding weight.  If

`2^(a-1)+1 ≤ TotalWeight < 2 * weight(r)`,

then the power-of-two weight of `r` forces its reduced support to have
cardinality at most `m+1-a`.  Equivalently, it omits at least `a-1` of the
`m` tail coordinates.  This is the first direct support-codimension bound
coming from the critical modulus inequality.
-/
import MinModulus.G1StrictMajorityGrowth

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A total weight floor and strict majority force a quantitative support
upper bound for the majority collision. -/
theorem support_card_add_le_of_weightFloor_and_strictMajority
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) (a : ℕ) (ha : 0 < a)
    (hfloor : 2 ^ (a - 1) + 1 ≤
      (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)))
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    (r.val.1 ∪ r.val.2).card + a ≤ m + 1 := by
  have hrle : (r.val.1 ∪ r.val.2).card ≤ m := by
    simpa using Finset.card_le_univ (r.val.1 ∪ r.val.2)
  have hpowlt : 2 ^ (a - 1) <
      2 ^ (m - (r.val.1 ∪ r.val.2).card + 1) := by
    calc
      2 ^ (a - 1) < 2 ^ (a - 1) + 1 := by omega
      _ ≤ (canonicalReducedCollisions (g := g) hh).sum
          (reducedCollisionWeight (m := m)) := hfloor
      _ < 2 * reducedCollisionWeight (m := m) r := hmajor
      _ = 2 ^ (m - (r.val.1 ∪ r.val.2).card + 1) := by
        simp [reducedCollisionWeight, pow_succ, Nat.mul_comm]
  have hexp : a - 1 < m - (r.val.1 ∪ r.val.2).card + 1 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hpowlt
  omega

/-- Equivalent complement form: the majority collision has at least `a-1`
unused tail coordinates available for padding. -/
theorem pred_le_compl_support_card_of_weightFloor_and_strictMajority
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h) (a : ℕ) (ha : 0 < a)
    (hfloor : 2 ^ (a - 1) + 1 ≤
      (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)))
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    a - 1 ≤ m - (r.val.1 ∪ r.val.2).card := by
  have hs := support_card_add_le_of_weightFloor_and_strictMajority
    hh r a ha hfloor hmajor
  omega

end MinModulus
