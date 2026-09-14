# Neighbors outside a full positive affine domain

For a valid tuple in a nonzero cyclic group with injective doubling, fix
an offset t and let S be the full positive affine domain. A represented
neighbor of an outside coordinate a is an i in S for which
2*(g(a)-g(i)) is a coordinate difference.

Four generic results are proved:

* The full domain admits a total coordinate map realizing g(f(i))+t=2*g(i)
  on S. This choice also works for an empty coordinate type.
* Every represented neighbor set R of an outside coordinate satisfies
  |R|<=6 or |R|+|S|<=n+1.
* Neighbor sets of size at least seven belonging to distinct outside
  coordinates intersect in at most one coordinate.
* For any represented neighbor sets A and B of distinct outside
  coordinates, |S|<=|S\A|+|S\B|+6.

The statements retain the outside-domain, representation, validity and
injective-doubling hypotheses. Neighbor sets need not contain every
represented neighbor. The proofs specialize the existing propagation
results using membership witnesses in the full domain.

All four original proofs, eight exact declaration types and two existing
definition values pass both installed Lean/Mathlib revisions with only
standard axioms. Temporary file links are flattened so compilation does
not encounter the operating system's symlink depth limit. No full Lake
build is required.

The next step is to count missing incidences and average the pairwise
bound. A bound of one on the domain complement is not yet proved.
Absolute central inequalities and generic G1/G2/G3 remain open.
Split Prove2Me export and private publication remain.

## Verified Prove2Me dense-case chain

These results are included in the fourteen-theorem dense positive-domain
chain, now private and Proved. See [the consolidated chain](DensePositiveDomainResearch.md).
The density premise is explicit, and unrestricted G1/G2/G3 remain open.
