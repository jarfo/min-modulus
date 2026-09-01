/-
# Linear incidence packing after the parity split

On a parity class the adjacent-nesting term vanishes.  The sharp second
moment then has the same positive-upper incidence mass as a factor on both
sides.  Cancelling that factor gives

  `2 S_p <= (|F_p|+1) |U_p|`.

The large-support factor-eight supply `8 W_p <= S_p` therefore yields the
linear packing `16 W_p <= (|F_p|+1)|U_p|` for each parity.

Summing the even and odd inequalities does not lose the factor four used by
selecting a single heavy parity: both parity unions lie in the full union and
the two vertex counts add to `|F|`.  The result is the residual-free global
bound

  `16 W <= (|F|+2)|U|`.

Thus all cross-cardinality duplication is absorbed with a constant overhead
of two color classes.
-/
import MinModulus.G1PositiveUpperParityPacking

namespace MinModulus

open Finset

variable {m : ℕ} {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- If the adjacent face term vanishes, cancel the positive-upper incidence
factor from the sharp second moment. -/
theorem two_mul_positiveUpperIncidenceMass_le_card_succ_mul_union_of_adjacent_zero
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (hadjZero : reducedCollisionAdjacentPositiveNestingFaceMass F = 0) :
    2 * reducedCollisionPositiveUpperIncidenceMass F ≤
      (F.card + 1) *
        (reducedCollisionPositiveUpperValueUnionAll F).card := by
  let S := reducedCollisionPositiveUpperIncidenceMass F
  let U := (reducedCollisionPositiveUpperValueUnionAll F).card
  by_cases hS : S = 0
  · simp [S, hS]
  · have hSpos : 0 < S := Nat.pos_of_ne_zero hS
    have hbase :=
      two_mul_positiveUpperIncidenceMass_sq_le_union_mul_adjacentNestingBudget
        hg F
    have hmul : (2 * S) * S ≤ ((F.card + 1) * U) * S := by
      calc
        (2 * S) * S = 2 * S ^ 2 := by ring
        _ ≤ U * (F.card * S + S + 0) := by
          simpa [S, U, hadjZero] using hbase
        _ = ((F.card + 1) * U) * S := by ring
    exact Nat.le_of_mul_le_mul_right hmul hSpos

/-- The even parity class has linear coefficient sixteen after incidence
cancellation and factor-eight supply. -/
theorem sixteen_mul_evenPositiveCardWeight_le_card_succ_mul_union
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonicalCard : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    let E := reducedCollisionEvenPositiveCardSubfamily F
    16 * E.sum (reducedCollisionWeight (m := m)) ≤
      (E.card + 1) *
        (reducedCollisionPositiveUpperValueUnionAll E).card := by
  classical
  let E := reducedCollisionEvenPositiveCardSubfamily F
  change 16 * E.sum (reducedCollisionWeight (m := m)) ≤
    (E.card + 1) *
      (reducedCollisionPositiveUpperValueUnionAll E).card
  have hcardE : ∀ q ∈ E, q.val.1.card ≤ q.val.2.card := by
    intro q hq
    exact hcanonicalCard q
      (mem_reducedCollisionEvenPositiveCardSubfamily_iff.mp hq).1
  have hsixE : ∀ q ∈ E, 6 ≤ (reducedCollisionSupport q).card := by
    intro q hq
    exact hsix q (mem_reducedCollisionEvenPositiveCardSubfamily_iff.mp hq).1
  have hsupply := eight_mul_sum_weight_le_positiveUpperIncidenceMass
    hg E hcardE hsixE
  have hinc :=
    two_mul_positiveUpperIncidenceMass_le_card_succ_mul_union_of_adjacent_zero
      hg E (adjacentPositiveNestingFaceMass_evenPositiveCard_eq_zero F)
  calc
    16 * E.sum (reducedCollisionWeight (m := m)) =
        2 * (8 * E.sum (reducedCollisionWeight (m := m))) := by ring
    _ ≤ 2 * reducedCollisionPositiveUpperIncidenceMass E :=
      Nat.mul_le_mul_left 2 hsupply
    _ ≤ (E.card + 1) *
        (reducedCollisionPositiveUpperValueUnionAll E).card := hinc

/-- The odd parity class has the same linear coefficient sixteen. -/
theorem sixteen_mul_oddPositiveCardWeight_le_card_succ_mul_union
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonicalCard : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    let O := reducedCollisionOddPositiveCardSubfamily F
    16 * O.sum (reducedCollisionWeight (m := m)) ≤
      (O.card + 1) *
        (reducedCollisionPositiveUpperValueUnionAll O).card := by
  classical
  let O := reducedCollisionOddPositiveCardSubfamily F
  change 16 * O.sum (reducedCollisionWeight (m := m)) ≤
    (O.card + 1) *
      (reducedCollisionPositiveUpperValueUnionAll O).card
  have hcardO : ∀ q ∈ O, q.val.1.card ≤ q.val.2.card := by
    intro q hq
    exact hcanonicalCard q
      (mem_reducedCollisionOddPositiveCardSubfamily_iff.mp hq).1
  have hsixO : ∀ q ∈ O, 6 ≤ (reducedCollisionSupport q).card := by
    intro q hq
    exact hsix q (mem_reducedCollisionOddPositiveCardSubfamily_iff.mp hq).1
  have hsupply := eight_mul_sum_weight_le_positiveUpperIncidenceMass
    hg O hcardO hsixO
  have hinc :=
    two_mul_positiveUpperIncidenceMass_le_card_succ_mul_union_of_adjacent_zero
      hg O (adjacentPositiveNestingFaceMass_oddPositiveCard_eq_zero F)
  calc
    16 * O.sum (reducedCollisionWeight (m := m)) =
        2 * (8 * O.sum (reducedCollisionWeight (m := m))) := by ring
    _ ≤ 2 * reducedCollisionPositiveUpperIncidenceMass O :=
      Nat.mul_le_mul_left 2 hsupply
    _ ≤ (O.card + 1) *
        (reducedCollisionPositiveUpperValueUnionAll O).card := hinc

omit [DecidableEq G] in
/-- The two parity filters partition the family cardinality exactly. -/
theorem card_evenPositiveCard_add_card_oddPositiveCard
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    (reducedCollisionEvenPositiveCardSubfamily F).card +
        (reducedCollisionOddPositiveCardSubfamily F).card = F.card := by
  classical
  simpa [reducedCollisionEvenPositiveCardSubfamily,
    reducedCollisionOddPositiveCardSubfamily] using
      Finset.card_filter_add_card_filter_not
        (s := F) (fun q : ReducedSubsetSumCollision g h ↦ Even q.val.1.card)

/-- The even parity upper union is contained in the full-family upper union. -/
theorem evenPositiveCardUpperUnion_subset_all
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionPositiveUpperValueUnionAll
        (reducedCollisionEvenPositiveCardSubfamily F) ⊆
      reducedCollisionPositiveUpperValueUnionAll F := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨q, hq, hxq⟩
  exact Finset.mem_biUnion.mpr ⟨q,
    (mem_reducedCollisionEvenPositiveCardSubfamily_iff.mp hq).1, hxq⟩

/-- The odd parity upper union is contained in the full-family upper union. -/
theorem oddPositiveCardUpperUnion_subset_all
    {g : Fin (m + 1) → G} {h : G}
    (F : Finset (ReducedSubsetSumCollision g h)) :
    reducedCollisionPositiveUpperValueUnionAll
        (reducedCollisionOddPositiveCardSubfamily F) ⊆
      reducedCollisionPositiveUpperValueUnionAll F := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨q, hq, hxq⟩
  exact Finset.mem_biUnion.mpr ⟨q,
    (mem_reducedCollisionOddPositiveCardSubfamily_iff.mp hq).1, hxq⟩

/-- Summing the two parity packings gives a residual-free all-rank theorem
with only a two-color overhead. -/
theorem sixteen_mul_sum_weight_le_card_add_two_mul_positiveUpperUnion
    {g : Fin (m + 1) → G} (hg : ValidTuple g) {h : G}
    (F : Finset (ReducedSubsetSumCollision g h))
    (hcanonicalCard : ∀ q ∈ F, q.val.1.card ≤ q.val.2.card)
    (hsix : ∀ q ∈ F, 6 ≤ (reducedCollisionSupport q).card) :
    16 * F.sum (reducedCollisionWeight (m := m)) ≤
      (F.card + 2) *
        (reducedCollisionPositiveUpperValueUnionAll F).card := by
  classical
  let E := reducedCollisionEvenPositiveCardSubfamily F
  let O := reducedCollisionOddPositiveCardSubfamily F
  let U := (reducedCollisionPositiveUpperValueUnionAll F).card
  have hE := sixteen_mul_evenPositiveCardWeight_le_card_succ_mul_union
    hg F hcanonicalCard hsix
  have hO := sixteen_mul_oddPositiveCardWeight_le_card_succ_mul_union
    hg F hcanonicalCard hsix
  have hEsub := evenPositiveCardUpperUnion_subset_all F
  have hOsub := oddPositiveCardUpperUnion_subset_all F
  have hEcard :
      (reducedCollisionPositiveUpperValueUnionAll E).card ≤ U :=
    Finset.card_le_card hEsub
  have hOcard :
      (reducedCollisionPositiveUpperValueUnionAll O).card ≤ U :=
    Finset.card_le_card hOsub
  have hweights := sum_evenPositiveCard_add_sum_oddPositiveCard F
    (reducedCollisionWeight (m := m))
  have hcards := card_evenPositiveCard_add_card_oddPositiveCard F
  calc
    16 * F.sum (reducedCollisionWeight (m := m)) =
        16 * E.sum (reducedCollisionWeight (m := m)) +
          16 * O.sum (reducedCollisionWeight (m := m)) := by
      rw [← hweights]
      ring
    _ ≤ (E.card + 1) *
          (reducedCollisionPositiveUpperValueUnionAll E).card +
        (O.card + 1) *
          (reducedCollisionPositiveUpperValueUnionAll O).card :=
      Nat.add_le_add hE hO
    _ ≤ (E.card + 1) * U + (O.card + 1) * U :=
      Nat.add_le_add
        (Nat.mul_le_mul_left (E.card + 1) hEcard)
        (Nat.mul_le_mul_left (O.card + 1) hOcard)
    _ = (F.card + 2) * U := by
      rw [← hcards]
      ring

section CriticalParityIncidence

/-- Milestone 2df: the complete non-root genuine critical family has a
residual-free linear positive-upper packing across all positive-tail ranks. -/
theorem genuineDominant_liveRoot_largeSupport_positiveUpper_parityIncidence
    {n s q : ℕ} (hqodd : Odd q)
    (g : Fin (n + 1) → ZMod (2 ^ (s + 1) * q)) (hg : ValidTuple g)
    (r : ReducedSubsetSumCollision g
      ((2 ^ s * q : ℕ) : ZMod (2 ^ (s + 1) * q)))
    (hr : r ∈ criticalCanonicalReducedCollisions g)
    (hres : IsCriticalGenuineDominantEscapeCollision g r)
    (hAcard : r.val.1.card = 1)
    (hBcard : r.val.2.card = 2) :
    let F := criticalCanonicalNonrootCollisions g r
    16 * F.sum (reducedCollisionWeight (m := n)) ≤
        (F.card + 2) *
          (reducedCollisionPositiveUpperValueUnionAll F).card ∧
      (reducedCollisionPositiveUpperValueUnionAll F).card ≤ 2 ^ n := by
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
  refine ⟨sixteen_mul_sum_weight_le_card_add_two_mul_positiveUpperUnion
      hg F hcanonicalCard hsix, ?_⟩
  calc
    (reducedCollisionPositiveUpperValueUnionAll F).card ≤
        (subsetSumRange g).card := Finset.card_le_card
          (reducedCollisionPositiveUpperValueUnionAll_subset_subsetSumRange F)
    _ = 2 ^ n := card_subsetSumRange g hg

end CriticalParityIncidence

end MinModulus
