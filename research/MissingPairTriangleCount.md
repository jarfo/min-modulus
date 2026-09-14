# Triangle lower bound from missing coordinate pairs

For a family D of two-element coordinate subsets, a fixed member P of D
is contained in at most n-2 three-element supports. Delete P from each
containing triple to inject those triples into the one-element subsets
of the complement of P.

Consequently, if Ts contains every three-element support avoiding every
pair in D, then

    binomial(n,3) <= |Ts|+(n-2)*|D|.

The proof bounds the union of triples containing a missing pair. It does
not require a group, a valid tuple, or a disjointness hypothesis on D.
The two-element condition on D and the coverage condition on Ts are
explicit.

To apply this to represented doubled differences, take D to cover all
unrepresented coordinate pairs and Ts to contain all represented
triangles. That application and extraction of a large positive affine
domain remain open, as do absolute central inequalities and generic
G1/G2/G3.

Both original proofs pass both Mathlib revisions. Both exact declaration
types agree, with standard Lean axioms only. No new definition is
introduced. Both results are now verified privately on Prove2Me and integrated
into the consolidated DAG.


## Verified Prove2Me missing-pair triangle count chain

Both missing-pair triangle counting results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify both original target types and dependency sets. Every
original proof body is retained. No definition bundle, inline helper or
external theorem interface is required. One supporting root retains
both results.

The consolidated DAG has 1154 nodes and 2643 edges. All 766 exact proof dependency sets across 49 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Absolute central inequalities and generic G1/G2/G3 remain open.

* pair_containing_triples_card_le: f8d8df7b-d448-49e1-8464-3e7455c9c78f
* triangle_family_card_add_missing_pair_bound: 9a80d68f-187d-49b6-b6bb-ee89e0859819
