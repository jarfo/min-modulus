# Total count of represented triangles

A represented triangle is a three-element coordinate support whose
pairwise doubled differences are coordinate differences of the tuple.
For a valid cyclic tuple with injective doubling and a bound M on every
full positive affine domain, the main result is

    6*|Ts| <= (2*(M-2)+(n-2)+6)*binomial(n,2)

for any finite family Ts of represented supports. Subtraction is natural
subtraction. The nonzero cyclic modulus and domain-size bound are explicit.

Three proved steps assemble the earlier results.

1. Every represented support is contained in a full positive domain,
   contained in a full negative domain, or has a parametrized L-shape
   witness. A Fin 3 parametrization converts the coordinate-level
   classification into the exact exceptional-family count interface.
2. Supports contained in no affine domain have cardinality at most
   binomial(n,2). These first two results hold in any additive commutative
   group with injective doubling.
3. At a nonzero cyclic modulus, cover Ts by positive-domain triangles,
   negative-domain triangles and the remainder. Bound the first two
   families by the proved affine-domain counts and the remainder by
   the exceptional count. Overlap between positive and negative families
   does not affect this upper bound.

This assembles the total upper bound. A lower bound on represented
triangles in terms of missing pairs is still needed to force a large
positive domain. That density extraction, the absolute central
inequalities and generic G1/G2/G3 remain open.

All three original proofs pass both Mathlib revisions. Ten exact
declaration types and three definition values agree: ValidTuple and the
two affine-domain definitions. Only standard Lean axioms occur. No new
definition is introduced. Split Prove2Me export and publication remain.

## Verified three-theorem represented-triangle count export

All three original proofs have a verified split export on both revisions.
Three exact target types and dependency sets, four external interface
types and three existing definition values agree. No inline helper or
new definition is required. Metadata and live preflight pass; publication
is pending. The representation and positive-domain size bound remain
explicit. Controlling coordinates outside large domains, absolute
central inequalities and generic G1/G2/G3 remain open.
