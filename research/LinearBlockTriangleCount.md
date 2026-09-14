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
definition is introduced. Split Prove2Me export and publication remain.

## Verified two-theorem linear block count export

Both block-family counting statements and original proof bodies have
a verified split export on both revisions. Both exact target types and
dependency sets agree. No definition bundle, inline helper or external
theorem interface is required. Metadata and live preflight pass;
publication is pending. The intersection and largest-block hypotheses
remain explicit. Affine-domain assembly, large-domain extraction, the
absolute central inequalities and generic G1/G2/G3 remain open.
