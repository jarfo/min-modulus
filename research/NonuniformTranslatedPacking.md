# Nonuniform packing for translated support pairs

Four generic lemmas extend the translated-squarefree intersection method
beyond a single fixed support size.

For a valid tuple in an additive commutative group, consider disjoint
pairs (U,V) with the same signed value sum(V)-sum(U)=t and the same
nonnegative cardinality gap |U|=|V|+delta. Their separating-permutation
events are pairwise disjoint even when |U| and |V| vary. Consequently
the sum of their event cardinalities is at most n!.

More generally, assign each pair a natural weight w(U,V). If

    w(U,V)*choose(|U|+|V|,|U|) <= M

for every family member, then sum w(U,V)<=M. This follows from the exact
permutation-event cardinality and cancellation of n!, without division.
No doubling-injectivity assumption is needed for these two results.

With injective doubling, two disjoint pairs with equal signed value,
equal first-side cardinality and the same union must coincide. Hence a
family with |U|=|V|=j supported in A also has at most choose(|A|,2*j)
members. This complements the earlier choose(2*j,j) permutation bound.

All four original proofs, ten exact declaration types and two existing
definition values pass both installed Lean/Mathlib revisions with only
standard axioms. No new definition is introduced. The supported source
port omits an unused separated-pair definition, so the proofs use the
existing uncrossing lemma directly.

The next step decomposes an arbitrary-degree translation match into its
disjoint difference supports and common intersection. The weights should
count possible common intersections. The resulting numerical bound must
still be shown strong enough for the central-degree target. These lemmas
do not establish the unrestricted conjecture; G1/G2/G3 remain open.
Split Prove2Me export and private publication remain.

## Verified Prove2Me nonuniform translation chain

These results are included in the eight-theorem nonuniform translation
chain, now private and Proved. See [the consolidated chain](NonuniformTranslationResearch.md).
The numerical premise is explicit, and unrestricted G1/G2/G3 remain open.
