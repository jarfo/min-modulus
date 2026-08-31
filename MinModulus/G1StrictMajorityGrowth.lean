/-
# Strict majority forces strict support growth

If one canonical collision has more than half of the total padding weight,
no other canonical collision can have the same weight.  Because padding
weights are powers of two indexed by complementary support size, every other
shape has strictly larger reduced support and at most half the dominant
weight.

For escape targets this strict support growth also improves the previous
external-support charge: the number of new external coordinates is strictly
larger than the number of source negative-tail coordinates avoided.
-/
import MinModulus.G1DominantStarCrossing

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- A strict-majority canonical collision has strictly larger weight than
every other canonical collision. -/
theorem canonical_weight_lt_of_total_lt_two_weight
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r q : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hq : q ∈ canonicalReducedCollisions (g := g) hh)
    (hqr : q ≠ r)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    reducedCollisionWeight (m := m) q <
      reducedCollisionWeight (m := m) r := by
  classical
  let collisions := canonicalReducedCollisions (g := g) hh
  let weight : ReducedSubsetSumCollision g h → ℕ :=
    reducedCollisionWeight (m := m)
  have hqerase : q ∈ collisions.erase r :=
    Finset.mem_erase.mpr ⟨hqr, hq⟩
  have hqle : weight q ≤ (collisions.erase r).sum weight :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hqerase
  have hsum : (collisions.erase r).sum weight + weight r =
      collisions.sum weight := Finset.sum_erase_add collisions weight hr
  change collisions.sum weight < 2 * weight r at hmajor
  change weight q < weight r
  omega

omit [DecidableEq G] in
/-- Strict padding-weight loss is exactly strict growth of reduced support. -/
theorem reducedCollision_support_card_lt_of_weight_lt
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hweight : reducedCollisionWeight (m := m) q <
      reducedCollisionWeight (m := m) r) :
    (r.val.1 ∪ r.val.2).card < (q.val.1 ∪ q.val.2).card := by
  have hrle : (r.val.1 ∪ r.val.2).card ≤ m := by
    simpa using Finset.card_le_univ (r.val.1 ∪ r.val.2)
  have hqle : (q.val.1 ∪ q.val.2).card ≤ m := by
    simpa using Finset.card_le_univ (q.val.1 ∪ q.val.2)
  have hexp : m - (q.val.1 ∪ q.val.2).card <
      m - (r.val.1 ∪ r.val.2).card :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp
      (by simpa [reducedCollisionWeight] using hweight)
  omega

omit [DecidableEq G] in
/-- One unit of strict support growth costs at least a factor two in exact
padding weight. -/
theorem two_mul_reducedCollisionWeight_le_of_support_card_lt
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hsupport : (r.val.1 ∪ r.val.2).card <
      (q.val.1 ∪ q.val.2).card) :
    2 * reducedCollisionWeight (m := m) q ≤
      reducedCollisionWeight (m := m) r := by
  have hrle : (r.val.1 ∪ r.val.2).card ≤ m := by
    simpa using Finset.card_le_univ (r.val.1 ∪ r.val.2)
  have hqle : (q.val.1 ∪ q.val.2).card ≤ m := by
    simpa using Finset.card_le_univ (q.val.1 ∪ q.val.2)
  have hexp : m - (q.val.1 ∪ q.val.2).card + 1 ≤
      m - (r.val.1 ∪ r.val.2).card := by
    omega
  have hpow := Nat.pow_le_pow_right (by norm_num : 0 < (2 : ℕ)) hexp
  simpa [reducedCollisionWeight, pow_succ, Nat.mul_comm] using hpow

/-- Every non-dominant canonical collision has strictly larger support and at
most half the dominant padding weight. -/
theorem canonical_other_support_growth_of_strictMajority
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r) :
    ∀ q ∈ canonicalReducedCollisions (g := g) hh, q ≠ r →
      (r.val.1 ∪ r.val.2).card < (q.val.1 ∪ q.val.2).card ∧
        2 * reducedCollisionWeight (m := m) q ≤
          reducedCollisionWeight (m := m) r := by
  intro q hq hqr
  have hweight := canonical_weight_lt_of_total_lt_two_weight
    hh r q hr hq hqr hmajor
  have hsupport := reducedCollision_support_card_lt_of_weight_lt r q hweight
  exact ⟨hsupport,
    two_mul_reducedCollisionWeight_le_of_support_card_lt r q hsupport⟩

omit [DecidableEq G] in
/-- Under strict support growth, external target support strictly exceeds the
source negative-tail fiber it can absorb. -/
theorem card_sourceTail_sdiff_lt_card_externalSupport_of_support_card_lt
    {g : Fin (m + 1) → G} {h : G}
    (r q : ReducedSubsetSumCollision g h)
    (hcard : (r.val.1 ∪ r.val.2).card <
      (q.val.1 ∪ q.val.2).card) :
    (r.val.2 \ (q.val.1 ∪ q.val.2)).card <
      ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).card := by
  have hsubset : r.val.2 \ (q.val.1 ∪ q.val.2) ⊆
      (r.val.1 ∪ r.val.2) \ (q.val.1 ∪ q.val.2) := by
    intro j hj
    exact Finset.mem_sdiff.mpr
      ⟨Finset.mem_union_right _ (Finset.mem_sdiff.mp hj).1,
        (Finset.mem_sdiff.mp hj).2⟩
  calc
    (r.val.2 \ (q.val.1 ∪ q.val.2)).card ≤
        ((r.val.1 ∪ r.val.2) \ (q.val.1 ∪ q.val.2)).card :=
      Finset.card_mono hsubset
    _ < ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).card :=
      Finset.card_sdiff_lt_card_sdiff_iff.mpr hcard

/-- Every target actually appearing in the escape incidence of a
strict-majority center grows support, loses at least half the padding weight,
and has strictly more external coordinates than absorbed source coordinates. -/
theorem canonicalSupportEscapeTarget_growth_of_strictMajority
    {g : Fin (m + 1) → G} {h : G} (hh : h + h = 0)
    (r : ReducedSubsetSumCollision g h)
    (hr : r ∈ canonicalReducedCollisions (g := g) hh)
    (hmajor : (canonicalReducedCollisions (g := g) hh).sum
        (reducedCollisionWeight (m := m)) <
      2 * reducedCollisionWeight (m := m) r)
    {j : Fin m} {q : ReducedSubsetSumCollision g h}
    (hjq : (j, q) ∈ canonicalSupportEscapeIncidences hh r) :
    (r.val.1 ∪ r.val.2).card < (q.val.1 ∪ q.val.2).card ∧
      2 * reducedCollisionWeight (m := m) q ≤
        reducedCollisionWeight (m := m) r ∧
      (r.val.2 \ (q.val.1 ∪ q.val.2)).card <
        ((q.val.1 ∪ q.val.2) \ (r.val.1 ∪ r.val.2)).card := by
  have hjq' := mem_canonicalSupportEscapeIncidences_iff.mp hjq
  have hqr := reducedCollision_ne_of_right_mem_of_avoids
    r q hjq'.1 hjq'.2.2.1
  have hgrowth := canonical_other_support_growth_of_strictMajority
    hh r hr hmajor q hjq'.2.1 hqr
  exact ⟨hgrowth.1, hgrowth.2,
    card_sourceTail_sdiff_lt_card_externalSupport_of_support_card_lt
      r q hgrowth.1⟩

end MinModulus
