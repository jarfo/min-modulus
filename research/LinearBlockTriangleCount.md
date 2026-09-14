# Pair and triangle counts in linear block families

Let F be a finite family of subsets of Fin n. Assume that distinct
members of F intersect in at most one coordinate.

The two proved results in LinearBlockTriangleCount.lean are

    sum_{S in F} binomial(|S|,2) <= binomial(n,2),
    3*sum_{S in F} binomial(|S|,3) <= (M-2)*binomial(n,2)

when every member S of F has |S|<=M. All subtraction is natural-number
subtraction; the formulas also include empty and small blocks.

The first bound counts the disjoint two-element powersets of the blocks
inside all two-element coordinate subsets. The second uses
3*binomial(s,3)=(s-2)*binomial(s,2) and the size bound.

These are purely combinatorial results. To apply them to the generic
min-modulus proof, the relevant families of positive and negative affine
domains still have to be defined and shown to satisfy the hypotheses.
The negative size bound is already available, but the assembly with
represented-triangle counting and large-domain extraction is unfinished.
Absolute central inequalities and generic G1/G2/G3 remain open.

Both original proofs pass both Mathlib revisions. The two exact
declaration types agree and only standard Lean axioms occur. No new
definition is introduced. Both results are now verified privately on Prove2Me and integrated
into the consolidated DAG.


## Verified Prove2Me linear block count chain

Both linear block counting results are private and Proved. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify both original target types and dependency sets. Every original
proof body is retained. No definition bundle, inline helper or external
theorem interface is required. One supporting root retains both results.

The consolidated DAG has 1132 nodes and 2597 edges. All 755 exact proof dependency sets across 46 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Large-domain extraction, absolute central inequalities and generic G1/G2/G3 remain open.

* linear_block_family_sum_choose_two_le: 3a0e7cce-be18-4378-a407-e76f0839b3bc
* linear_block_family_sum_choose_three_le: bc195050-9b7e-40a3-bf08-27366462dbb2
