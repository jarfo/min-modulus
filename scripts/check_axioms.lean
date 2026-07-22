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
