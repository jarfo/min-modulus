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
definition is introduced. All three results are now verified privately on Prove2Me and integrated
into the consolidated DAG.


## Verified Prove2Me represented-triangle count chain

All three represented-triangle counting results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify three original target types and dependency sets, four
external interface types and three existing definition values. Every
original proof body is retained. No inline helper or new definition
bundle is required. One supporting root retains all three results.

The consolidated DAG has 1151 nodes and 2641 edges. All 764 exact proof dependency sets across 48 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Controlling coordinates outside large domains, absolute central inequalities and generic G1/G2/G3 remain open.

* represented_triangle_support_trichotomy: 365cba63-8885-446d-a391-84cf69dc3d42
* represented_triangle_family_outside_affine_card_le: 2cb4f84e-2cae-4944-ae14-5484f9885624
* represented_triangle_family_card_upper_bound: d1ccfe28-bde8-4d5e-8e57-58fd6a08b71e
