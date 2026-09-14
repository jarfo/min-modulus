# One-escape structure from few missing pairs

Let g be a valid tuple of length n in a nonzero cyclic group, and assume
doubling is injective. Let D be a finite family of two-coordinate
subsets covering every pair whose doubled difference is not a coordinate
difference. D may also contain represented pairs.

For every n>=144, the explicit density condition

    (n-9)*|D| < 3*choose(n,2)

forces an offset t for which the full positive affine domain omits at
most one coordinate. Consequently there are a coordinate a and an offset
b such that every i different from a satisfies

    exists j, g(j)=2*g(i)+b.

Three generic lemmas prove this result. First, a full domain of size M
with n<2*M+40 has complement size at most one under the density condition.
The proof injects missing outside-inside incidences into D, averages the
pairwise missing-neighbor bound, and applies the scalar bounds that give
first at most twelve outside coordinates and then at most one. Second,
the previously proved triangle counts supply such a domain. Third, the
small complement gives an actual exceptional coordinate and offset.

All three original proofs, twelve exact declaration types and two
existing definition values pass both installed Lean/Mathlib revisions
with only standard axioms. No finite enumeration is used. No new
definition is introduced.

The next step applies the existing AlmostDoubling modulus theorem.
The density premise is not established from a modulus upper bound;
tuples outside this dense regime remain unhandled. Absolute central
inequalities and generic G1/G2/G3 remain open.
Split Prove2Me export and private publication remain.

## Verified Prove2Me dense-case chain

These results are included in the fourteen-theorem dense positive-domain
chain, now private and Proved. See [the consolidated chain](DensePositiveDomainResearch.md).
The density premise is explicit, and unrestricted G1/G2/G3 remain open.
