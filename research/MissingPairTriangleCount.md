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
introduced. Split Prove2Me export and publication remain.
