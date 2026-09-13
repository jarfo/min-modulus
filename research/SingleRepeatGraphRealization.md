# Actual single-repeat fibres and exact graph edge counts

[SingleRepeatGraphRealization.lean](SingleRepeatGraphRealization.lean)
provides two uniform interfaces for using the residual graph on actual
single-repeat fibres.

For every tuple g in an abelian group, degree k and value x, let
R=singleRepeatFibre g k x. The first theorem simultaneously chooses
residual supports B_a such that, for every a in R,

    |B_a|=k,    a not in B_a,    2g_a+sum_(B_a)g=x.

No validity or doubling assumption is needed for this existence result.
It follows by choosing the squarefree support in each fibre-membership
witness and deleting its repeated anchor.

The second theorem proves that a residual graph with two-element
supports has exactly |R| edges when g is valid, doubling is injective,
and all the anchor representations have the same value. This count
does not require support avoidance. Passing from an unordered edge to
its endpoint set is injective; its image is exactly the family of
residual supports. The previously proved uniqueness of the anchor of a
residual support then gives the count.

For k=2 these results, together with the existing endpoint-avoidance
theorem, supply an actual quartic fibre graph with |R| edges whose
endpoints lie outside R. The graph-walk interface to the even/odd cycle
encodings and the graph decomposition are still needed to prove the
proposed 2|R|<=n bound. The global repeated-sum growth inequality,
the single full-rank coefficient combination, and G1/G2/G3 remain open.

Both proofs pass the original and supported Mathlib revisions. Five
printed types and three definition values match exactly; all proof
axioms are standard and the source bodies are identical. Compilation
reuses the selective dependency caches and uses no finite enumeration.
These two results await their Prove2Me export and publication.

## Verified actual-fibre export

Both results now pass the original and supported revisions as separate
statement/proof pairs, with their original proof bodies retained. Both
original theorem types and exact dependency sets match. The three
definition types and values match; no proof holes occur outside declared
interfaces. The export adds one singleRepeatFibre definition bundle with
its direct membership interface and reuses the Proved anchor-uniqueness
theorem. Metadata, live readbacks and all three unused names pass.
These new nodes have not yet been uploaded. Graph-walk instantiation,
graph decomposition, the proposed half-dimension cap and G1/G2/G3 remain open.
