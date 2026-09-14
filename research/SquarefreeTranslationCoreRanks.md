# Squarefree translation counts grouped by core rank

For a fixed disjoint core size j, validity gives the separating-permutation
cap choose(2*j,j). When doubling is injective, the union-support injection
gives the independent cap choose(|A|,2*j).

The exact match count can be regrouped over any finite set J containing
all core sizes:

    |matches| = sum_(j in J) c_j * choose(|A|-2*j,k-j),

where c_j is the number of disjoint translation cores with first side
size j. This identity needs no validity. The two caps give

    |matches| <= sum_(j in J) min(choose(2*j,j),choose(|A|,2*j))
                             * choose(|A|-2*j,k-j).

A nonzero translation has no empty core, so J={1,...,k} gives an explicit
bound without a zero-core contribution. These formulas hold at arbitrary
dimension and degree. All group, validity, doubling-injectivity and rank
cover hypotheses remain explicit.

The rankwise sum does not use the joint nonuniform permutation budget.
A possible next improvement applies weighted packing to some ranks and
the support-union caps to the rest. No sufficiency for the central-degree
target is claimed; small positive core sizes still need stronger control.

Six original proofs, thirteen exact declaration types and three existing
definition values pass both installed Lean/Mathlib revisions with standard
axioms only. No new definition is introduced. G1/G2/G3 remain open.
Split Prove2Me export and private publication remain.
