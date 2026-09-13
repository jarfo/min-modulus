# Negative affine doubling domains

These three results constrain a possible structural case in the dense
represented-difference problem. They do not claim that a dense graph
has an affine block.

Let g be a valid tuple in an additive commutative group in which doubling
is injective. Suppose f is a partial negative affine doubling map on
S, expressed by

    g(f(i))+2*g(i)=t  for every i in S.

If f(i) also lies in S, applying the equation twice gives

    g(f(f(i)))+g(f(i))=2*g(i).

Pair-sum rigidity and injective doubling force f(i)=i. Conversely a
fixed point in S plainly maps into S. Thus a nonfixed image cannot stay
in the domain.

The map is injective on S: equal images cancel in the defining equation,
and then doubling injectivity and tuple injectivity identify their
preimages. Consequently the nonfixed part of S injects into the
complement of S. If F={i in S : f(i)=i}, then

    2*|S| <= n+|F|.

The fixed-point term is explicit. Fixed points satisfy 3*g(i)=t, but no
bound on their number is asserted here. In particular this file does
not silently rule out negative affine blocks when investigating dense
represented differences. Extraction of a large positive or negative
block from pair density remains unproved. The generic central bounds
and G1/G2/G3 remain open.

All three original proof bodies pass both Mathlib revisions. Six exact
declaration types and the ValidTuple definition value agree; the axiom
audit finds only standard Lean axioms. No new definition is introduced.
All three results are now verified privately on Prove2Me and integrated
into the consolidated DAG.


## Verified Prove2Me negative affine chain

All three negative affine domain results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify three original target types and dependency sets, two
external interface types, one original inline helper type and the
ValidTuple definition value. Every original proof body is retained.
No new definition bundle is introduced. One supporting root retains
the complete three-theorem chain.

The consolidated DAG has 1095 nodes and 2510 edges. All 736 exact proof dependency sets across 41 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The domain restrictions are proved. Affine structure
extraction, absolute central inequalities and generic G1/G2/G3 remain open.

* negative_affine_image_mem_domain_iff_fixed: 02925060-9408-4123-b963-1b265080ce78
* negative_affine_map_injOn: 71c88901-2693-4955-ac35-21e2fa84900d
* negative_affine_domain_twice_card_le_add_fixed: bf72659d-f12a-40fd-9b0d-ae0b30a72f01
