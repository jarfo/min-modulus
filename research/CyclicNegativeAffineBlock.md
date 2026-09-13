# Cyclic fixed points and negative affine closure

Four Lean results remove the fixed-point term from the preceding
negative affine domain bound.

For any valid tuple g at any nonzero cyclic modulus N, and any t, at
most two coordinates satisfy

    3*g_i=t.

No oddness or invertibility of three is assumed. For a coordinate in
this fibre, let q_i=floor(3*val(g_i)/N). Least representatives give

    3*val(g_i)=val(t)+N*q_i,    q_i in {0,1,2}.

Distinct fibre coordinates have distinct quotient labels. If three
existed, their labels would be 0,1,2 in some order. Adding the two
extreme representative equations and doubling the middle one produces
an arithmetic progression among three distinct coordinates, contradicting
pair-sum rigidity. Cancellation of three occurs in natural representatives,
so moduli divisible by three are included.

Now suppose g(f(i))+2*g_i=t on a finite domain S. Fixed points of f lie
in the triple fibre, hence there are at most two. Combining this with
the verified negative affine domain bound gives, whenever doubling is
injective,

    2*|S| <= n+2.

At odd modulus doubling is injective. A negative affine map closed on
the entire tuple would therefore imply n<=2. Thus such full negative
closure cannot occur for a valid tuple of dimension at least three.

These are structural restrictions. They do not extract an affine block
from dense represented doubled differences. The positive affine case,
the remaining quartic density argument, absolute central inequalities
and generic G1/G2/G3 remain open. Positive one-escape doubling already
has a separate proved theorem and is not reproved here.

All four original proofs pass both Mathlib revisions. Eight exact
declaration types and the ValidTuple definition value agree. The axiom
audit finds only standard Lean axioms. No new definition is introduced.
All four results are now verified privately on Prove2Me and integrated
into the consolidated DAG.


## Verified Prove2Me cyclic fixed-point chain

All four cyclic fixed-point results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, three
external interface types and the ValidTuple definition value. Every
original proof body is retained. No inline helper or new definition
bundle is introduced. One supporting root retains the complete
four-theorem chain.

The consolidated DAG has 1103 nodes and 2528 edges. All 740 exact proof dependency sets across 42 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Cyclic fixed-point control is proved. Affine structure extraction, absolute
central inequalities and generic G1/G2/G3 remain open.

* cyclic_triple_fibre_card_le_two: 4baa0aca-9934-4966-aa1c-a4c6ddd7a8be
* cyclic_negative_affine_fixed_card_le_two: 04cbeba0-c8c6-4614-92e0-0f994be09cec
* cyclic_negative_affine_domain_twice_card_le_add_two: d815e427-f53d-48c1-a744-5cad3c4c2e1d
* odd_valid_negative_affine_closed_dimension_le_two: 98f08e7e-363b-4d1e-8ce0-2fa1f1126ff7
