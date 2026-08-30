/-
Axiom audit for the main results.  Run with

    lake env lean scripts/check_axioms.lean

Every declaration below must depend only on the three standard Lean axioms
`propext`, `Classical.choice`, `Quot.sound`.  In particular `sorryAx` must
never appear.  CI (`.github/workflows/build.yml`) fails the build if it does.
-/
import MinModulus

-- Theorem A (validity / upper bound), Theorem B (optimality / lower bound),
-- and the main theorem `Nmin(n) = 2^n - 2^⌊log₂ n⌋`.
#print axioms MinModulus.theoremA
#print axioms MinModulus.theoremB
#print axioms MinModulus.nmin_eq

-- Proposition 2: optimality among elementary abelian 2-groups.
#print axioms MinModulus.elementaryAbelianTwoGroups_optimal

-- Inal's theorem (open problem 4): the exact minimum order for unique multiset
-- sums in finite abelian groups is `2^(n-1)`.
#print axioms MinModulus.card_ge          -- lower bound: valid ⟹ 2^m ≤ |G|
#print axioms MinModulus.elem_valid       -- sharpness: standard tuple is valid
#print axioms MinModulus.elem_card        -- the extremal group has order 2^m
#print axioms MinModulus.mab_isLeast      -- headline: m_ab(n) = 2^(n-1) (IsLeast)
#print axioms MinModulus.equality_classification  -- classification at equality
#print axioms MinModulus.equality_addEquiv        -- explicit φ : G ≃+ (ZMod 2)^m

-- Descent lemmas toward the global optimality conjecture (open problem 1):
-- combination and deletion for witnesses at an order-two element.
#print axioms MinModulus.validTuple_iff_no_zero_witness
#print axioms MinModulus.witness_combination        -- Lemma A
#print axioms MinModulus.quotient_valid_of_no_witness  -- halving branch
#print axioms MinModulus.deletion_descent           -- Lemma B
#print axioms MinModulus.pair_descent               -- the clean descent rung
#print axioms MinModulus.nat_card_quotient_two_smul -- |G/⟨h⟩| * 2 = |G|
#print axioms MinModulus.validTuple_comp            -- transport along injective maps
#print axioms MinModulus.quotZMultiplesEquivZMod    -- ZMod N / <M>  ≃+  ZMod M
#print axioms MinModulus.exists_validTuple_half_of_no_witness  -- halving, cyclic
#print axioms MinModulus.exists_validTuple_half_of_delete      -- deletion, cyclic
#print axioms MinModulus.exists_validTuple_half_of_pair        -- pair descent, cyclic
#print axioms MinModulus.card_ge_of_odd     -- odd order: |G| >= 2^m + 2m (m >= 3)
#print axioms MinModulus.card_ge_of_odd'    -- odd order: |G| >= 2^m + m
#print axioms MinModulus.valid_odd_zmod_bound
#print axioms MinModulus.odd_min_three      -- least odd valid modulus = 7 for n = 3
#print axioms MinModulus.odd_min_four       -- least odd valid modulus = 15 for n = 4 (G2, n <= 4)
