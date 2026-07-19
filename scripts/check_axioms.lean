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
