# Fractional packing and combined core-rank certificates

The nonuniform separating-permutation bound has an exact rational form:
for disjoint pairs (U,V) of fixed cardinality gap and signed evaluation
in a valid tuple,

    sum_(U,V) 1 / choose(|U|+|V|,|U|) <= 1.

The factorial event counts establish this without any asymptotic estimate.
For translation cores of size j, let c_j denote their number. Over any
finite set J containing all core sizes, the shared constraint is

    sum_(j in J) c_j / choose(2*j,j) <= 1.

With injective doubling, the independent bounds are

    c_j <= C_j := min(choose(2*j,j),choose(|A|,2*j)).

The exact match-count weight is w_j=choose(|A|-2*j,k-j). For any rational
alpha>=0 and nonnegative rational beta_j satisfying

    w_j <= alpha / choose(2*j,j) + beta_j,

the new certificate theorem proves

    |matches| <= alpha + sum_(j in J) C_j * beta_j.

Thus a numerical certificate may spend the shared fractional budget on
some ranks and use the independent caps for the remaining contribution.
No specific certificate sufficiently strong for the central-degree goal
is claimed. These premises remain explicit, and G1/G2/G3 remain open.

Four original proofs, fourteen exact declaration types and four existing
definition values pass both installed Lean/Mathlib revisions with only
standard axioms. No new definition is introduced. Split Prove2Me export
and private publication remain.
