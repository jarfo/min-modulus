/-
# Parity packing removes the adjacent-nesting residual

The sharp symmetric upper-face second moment charges only strict positive-tail
nesting of cardinality gap one.  Such an edge always changes the parity of the
positive-tail cardinality.  Splitting an arbitrary collision family into its
even and odd positive-cardinality subfamilies therefore removes every
adjacent edge inside either part.  Nesting gaps at least two were already paid
by the two face baselines, so each parity class has a residual-free global
packing.

One parity class carries at least half of the total padding weight.  The
factor-eight face supply and the second moment consequently give a coefficient
`32` for the full family, with no crossing or crowded-adjacent error.  This is
a general rank-coloring pattern; it replaces edge-by-edge fan aggregation for
the internal positive-upper union, at the cost of exactly the factor four from
selecting half the weight.
-/
import MinModulus.G1PositiveUpperAdjacentMultiplicity

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Collisions whose positive tail has even cardinality. -/
noncomputable def reducedCollisionEvenPositiveCardSubfamily
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) := by
  classical
  exact F.filter (fun q ↦ Even q.val.1.card)

/-- Collisions whose positive tail has odd cardinality, expressed as the
complement of even cardinality so the two filters partition exactly. -/
noncomputable def reducedCollisionOddPositiveCardSubfamily
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) := by
  classical
  exact F.filter (fun q ↦ ¬Even q.val.1.card)

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionEvenPositiveCardSubfamily_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {q : ReducedSubsetSumCollision g h} :
    q ∈ reducedCollisionEvenPositiveCardSubfamily F ↔
      q ∈ F ∧ Even q.val.1.card := by
  classical
  simp [reducedCollisionEvenPositiveCardSubfamily]

omit [DecidableEq G] in
@[simp] theorem mem_reducedCollisionOddPositiveCardSubfamily_iff
    {g : Fin (m + 1) → G} {h : G}
    {F : Finset (ReducedSubsetSumCollision g h)}
    {q : ReducedSubsetSumCollision g h} :
    q ∈ reducedCollisionOddPositiveCardSubfamily F ↔
      q ∈ F ∧ ¬Even q.val.1.card := by
  classical
  simp [reducedCollisionOddPositiveCardSubfamily]

omit [DecidableEq G] in
/-- The parity split partitions every weighted collision sum exactly. -/
theorem sum_evenPositiveCard_add_sum_oddPositiveCard
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (w : ReducedSubsetSumCollision g h → ℕ) :
    (reducedCollisionEvenPositiveCardSubfamily F).sum w +
        (reducedCollisionOddPositiveCardSubfamily F).sum w = F.sum w := by
  classical
  simpa [reducedCollisionEvenPositiveCardSubfamily,
    reducedCollisionOddPositiveCardSubfamily] using
      Finset.sum_filter_add_sum_filter_not F
        (fun q : ReducedSubsetSumCollision g h ↦ Even q.val.1.card) w

omit [DecidableEq G] in
/-- No adjacent positive-tail nesting edge has both endpoints in the even
positive-cardinality subfamily. -/
theorem adjacentPositiveNestingPairs_evenPositiveCard_eq_empty
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionAdjacentPositiveNestingPairs
      (reducedCollisionEvenPositiveCardSubfamily F) = ∅ := by
  classical
  ext p
  constructor
  · intro hp
    have hadj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hp
    have hnest :=
      mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
    have hq :=
      mem_reducedCollisionEvenPositiveCardSubfamily_iff.mp hnest.1
    have hu :=
      mem_reducedCollisionEvenPositiveCardSubfamily_iff.mp hnest.2.1
    have hu' : Even (p.1.val.1.card + 1) := by
      simpa [hadj.2] using hu.2
    exact False.elim ((Nat.even_add_one.mp hu') hq.2)
  · simp

omit [DecidableEq G] in
/-- No adjacent positive-tail nesting edge has both endpoints in the odd
positive-cardinality subfamily. -/
theorem adjacentPositiveNestingPairs_oddPositiveCard_eq_empty
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionAdjacentPositiveNestingPairs
      (reducedCollisionOddPositiveCardSubfamily F) = ∅ := by
  classical
  ext p
  constructor
  · intro hp
    have hadj :=
      mem_reducedCollisionAdjacentPositiveNestingPairs_iff.mp hp
    have hnest :=
      mem_reducedCollisionStrictPositiveNestingPairs_iff.mp hadj.1
    have hq :=
      mem_reducedCollisionOddPositiveCardSubfamily_iff.mp hnest.1
    have hu :=
      mem_reducedCollisionOddPositiveCardSubfamily_iff.mp hnest.2.1
    have huEven : Even p.2.val.1.card := by
      rw [hadj.2, Nat.even_add_one]
      exact hq.2
    exact False.elim (hu.2 huEven)
  · simp

/-- Consequently the adjacent face residual vanishes on the even class. -/
theorem adjacentPositiveNestingFaceMass_evenPositiveCard_eq_zero
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionAdjacentPositiveNestingFaceMass
      (reducedCollisionEvenPositiveCardSubfamily F) = 0 := by
  rw [reducedCollisionAdjacentPositiveNestingFaceMass,
    adjacentPositiveNestingPairs_evenPositiveCard_eq_empty]
  simp

/-- Consequently the adjacent face residual vanishes on the odd class. -/
theorem adjacentPositiveNestingFaceMass_oddPositiveCard_eq_zero
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionAdjacentPositiveNestingFaceMass
      (reducedCollisionOddPositiveCardSubfamily F) = 0 := by
  rw [reducedCollisionAdjacentPositiveNestingFaceMass,
    adjacentPositiveNestingPairs_oddPositiveCard_eq_empty]
  simp

/-- Residual-free factor-eight second-moment packing on the even positive-tail
rank class. -/
theorem oneHundredTwentyEight_mul_evenPositiveCardWeight_sq_le
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonicalCard : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    let E := reducedCollisionEvenPositiveCardSubfamily F
    128 * (E.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll E).card *
          (E.card * reducedCollisionPositiveUpperIncidenceMass E +
            reducedCollisionPositiveUpperIncidenceMass E) ∧
      (reducedCollisionPositiveUpperValueUnionAll E).card ≤ 2 ^ m := by
  classical
  let E := reducedCollisionEvenPositiveCardSubfamily F
  change 128 * (E.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll E).card *
        (E.card * reducedCollisionPositiveUpperIncidenceMass E +
          reducedCollisionPositiveUpperIncidenceMass E) ∧
    (reducedCollisionPositiveUpperValueUnionAll E).card ≤ 2 ^ m
  have hcardE : ∀ q ∈ E, q.val.1.card ≤ q.val.2.card := by
    intro q hq
    exact hcanonicalCard q
      (mem_reducedCollisionEvenPositiveCardSubfamily_iff.mp hq).1
  have hsixE : ∀ q ∈ E, 6 ≤ (reducedCollisionSupport q).card := by
    intro q hq
    exact hsix q (mem_reducedCollisionEvenPositiveCardSubfamily_iff.mp hq).1
  have hpack :=
    oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentNestingBudget
      hg E hcardE hsixE
  have hzero := adjacentPositiveNestingFaceMass_evenPositiveCard_eq_zero F
  refine ⟨?_, ?_⟩
  · simpa [E, hzero] using hpack
  · calc
      (reducedCollisionPositiveUpperValueUnionAll E).card ≤
          (subsetSumRange g).card := Finset.card_le_card
            (reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange E)
      _ = 2 ^ m := card_subsetSumRange g hg

/-- Residual-free factor-eight second-moment packing on the odd positive-tail
rank class. -/
theorem oneHundredTwentyEight_mul_oddPositiveCardWeight_sq_le
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonicalCard : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    let O := reducedCollisionOddPositiveCardSubfamily F
    128 * (O.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll O).card *
          (O.card * reducedCollisionPositiveUpperIncidenceMass O +
            reducedCollisionPositiveUpperIncidenceMass O) ∧
      (reducedCollisionPositiveUpperValueUnionAll O).card ≤ 2 ^ m := by
  classical
  let O := reducedCollisionOddPositiveCardSubfamily F
  change 128 * (O.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
      (reducedCollisionPositiveUpperValueUnionAll O).card *
        (O.card * reducedCollisionPositiveUpperIncidenceMass O +
          reducedCollisionPositiveUpperIncidenceMass O) ∧
    (reducedCollisionPositiveUpperValueUnionAll O).card ≤ 2 ^ m
  have hcardO : ∀ q ∈ O, q.val.1.card ≤ q.val.2.card := by
    intro q hq
    exact hcanonicalCard q
      (mem_reducedCollisionOddPositiveCardSubfamily_iff.mp hq).1
  have hsixO : ∀ q ∈ O, 6 ≤ (reducedCollisionSupport q).card := by
    intro q hq
    exact hsix q (mem_reducedCollisionOddPositiveCardSubfamily_iff.mp hq).1
  have hpack :=
    oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentNestingBudget
      hg O hcardO hsixO
  have hzero := adjacentPositiveNestingFaceMass_oddPositiveCard_eq_zero F
  refine ⟨?_, ?_⟩
  · simpa [O, hzero] using hpack
  · calc
      (reducedCollisionPositiveUpperValueUnionAll O).card ≤
          (subsetSumRange g).card := Finset.card_le_card
            (reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange O)
      _ = 2 ^ m := card_subsetSumRange g hg

omit [DecidableEq G] in
/-- At least one parity class carries at least half of the total padding
weight. -/
theorem sum_weight_le_two_mul_even_or_two_mul_odd
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    F.sum (reducedCollisionWeight (m := m)) ≤
        2 * (reducedCollisionEvenPositiveCardSubfamily F).sum
          (reducedCollisionWeight (m := m)) ∨
      F.sum (reducedCollisionWeight (m := m)) ≤
        2 * (reducedCollisionOddPositiveCardSubfamily F).sum
          (reducedCollisionWeight (m := m)) := by
  have hsum := sum_evenPositiveCard_add_sum_oddPositiveCard F
    (reducedCollisionWeight (m := m))
  omega

/-- Selecting the heavier parity class gives a residual-free coefficient-32
packing for the full family weight. -/
theorem thirtyTwo_mul_sum_weight_sq_le_even_or_odd_positiveUpper_packing
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonicalCard : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    let E := reducedCollisionEvenPositiveCardSubfamily F
    let O := reducedCollisionOddPositiveCardSubfamily F
    (32 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
          (reducedCollisionPositiveUpperValueUnionAll E).card *
            (E.card * reducedCollisionPositiveUpperIncidenceMass E +
              reducedCollisionPositiveUpperIncidenceMass E) ∧
        (reducedCollisionPositiveUpperValueUnionAll E).card ≤ 2 ^ m) ∨
      (32 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
          (reducedCollisionPositiveUpperValueUnionAll O).card *
            (O.card * reducedCollisionPositiveUpperIncidenceMass O +
              reducedCollisionPositiveUpperIncidenceMass O) ∧
        (reducedCollisionPositiveUpperValueUnionAll O).card ≤ 2 ^ m) := by
  classical
  let E := reducedCollisionEvenPositiveCardSubfamily F
  let O := reducedCollisionOddPositiveCardSubfamily F
  change (32 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll E).card *
          (E.card * reducedCollisionPositiveUpperIncidenceMass E +
            reducedCollisionPositiveUpperIncidenceMass E) ∧
      (reducedCollisionPositiveUpperValueUnionAll E).card ≤ 2 ^ m) ∨
    (32 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
        (reducedCollisionPositiveUpperValueUnionAll O).card *
          (O.card * reducedCollisionPositiveUpperIncidenceMass O +
            reducedCollisionPositiveUpperIncidenceMass O) ∧
      (reducedCollisionPositiveUpperValueUnionAll O).card ≤ 2 ^ m)
  have hE := oneHundredTwentyEight_mul_evenPositiveCardWeight_sq_le
    hg F hcanonicalCard hsix
  have hO := oneHundredTwentyEight_mul_oddPositiveCardWeight_sq_le
    hg F hcanonicalCard hsix
  rcases sum_weight_le_two_mul_even_or_two_mul_odd F with hheavy | hheavy
  · left
    refine ⟨?_, hE.2⟩
    change F.sum (reducedCollisionWeight (m := m)) ≤
      2 * E.sum (reducedCollisionWeight (m := m)) at hheavy
    have hsquare :
        32 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
          128 * (E.sum (reducedCollisionWeight (m := m))) ^ 2 := by
      calc
        32 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
            32 * (2 * E.sum (reducedCollisionWeight (m := m))) ^ 2 :=
          Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hheavy 2)
        _ = 128 * (E.sum (reducedCollisionWeight (m := m))) ^ 2 := by ring
    exact hsquare.trans hE.1
  · right
    refine ⟨?_, hO.2⟩
    change F.sum (reducedCollisionWeight (m := m)) ≤
      2 * O.sum (reducedCollisionWeight (m := m)) at hheavy
    have hsquare :
        32 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
          128 * (O.sum (reducedCollisionWeight (m := m))) ^ 2 := by
      calc
        32 * (F.sum (reducedCollisionWeight (m := m))) ^ 2 ≤
            32 * (2 * O.sum (reducedCollisionWeight (m := m))) ^ 2 :=
          Nat.mul_le_mul_left 32 (Nat.pow_le_pow_left hheavy 2)
        _ = 128 * (O.sum (reducedCollisionWeight (m := m))) ^ 2 := by ring
    exact hsquare.trans hO.1

section CriticalParityPacking

/-- Milestone 2de: the complete non-root genuine critical family admits a
residual-free positive-upper packing after selecting one parity of positive
tail rank. -/
theorem genuineDominant_liveRoot_largeSupport_positiveUpper_parityPacking
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    let E := reducedCollisionEvenPositiveCardSubfamily F
    let O := reducedCollisionOddPositiveCardSubfamily F
    (32 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
          (reducedCollisionPositiveUpperValueUnionAll E).card *
            (E.card * reducedCollisionPositiveUpperIncidenceMass E +
              reducedCollisionPositiveUpperIncidenceMass E) ∧
        (reducedCollisionPositiveUpperValueUnionAll E).card ≤ 2 ^ n) ∨
      (32 * (F.sum (reducedCollisionWeight (m := n))) ^ 2 ≤
          (reducedCollisionPositiveUpperValueUnionAll O).card *
            (O.card * reducedCollisionPositiveUpperIncidenceMass O +
              reducedCollisionPositiveUpperIncidenceMass O) ∧
        (reducedCollisionPositiveUpperValueUnionAll O).card ≤ 2 ^ n) := by
  classical
  letI : NeZero (2 ^ (s + 1) * q) :=
    ⟨(mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) (s + 1))
      (Odd.pos hqodd)).ne'⟩
  let hN : 2 ^ (s + 1) * q = 2 * (2 ^ s * q) := by
    rw [pow_succ]
    ring
  let hh := half_add_half hN
  let F := criticalCanonicalNonrootCollisions g r
  have hmem : ∀ v ∈ F,
      v ∈ criticalCanonicalReducedCollisions g ∧ v ≠ r := by
    intro v hv
    have hv' : v ∈ (criticalCanonicalReducedCollisions g).erase r := by
      simpa [F, criticalCanonicalNonrootCollisions] using hv
    have hv'' := Finset.mem_erase.mp hv'
    exact ⟨hv''.2, hv''.1⟩
  have hcanonicalCard : ∀ v ∈ F,
      v.val.1.card ≤ v.val.2.card := by
    intro v hv
    have hvcanonical : v ∈ canonicalReducedCollisions (g := g) hh := by
      simpa [hh, criticalCanonicalReducedCollisions] using (hmem v hv).1
    exact canonicalReducedCollision_card_le
      (mem_canonicalReducedCollisions_iff.mp hvcanonical)
  have hsix : ∀ v ∈ F, 6 ≤ (reducedCollisionSupport v).card := by
    intro v hv
    exact genuineDominant_liveRoot_all_other_support_card_six_le
      hqodd g hg r hr hres hAcard hBcard v
        (hmem v hv).1 (hmem v hv).2
  exact thirtyTwo_mul_sum_weight_sq_le_even_or_odd_positiveUpper_packing
    hg F hcanonicalCard hsix

end CriticalParityPacking

end MinModulus
