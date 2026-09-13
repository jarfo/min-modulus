# Quartic single-repeat fibres occupy at most half the coordinates

[QuarticFibreHalfBound.lean](QuarticFibreHalfBound.lean) proves, for every
valid tuple of n elements in an additive commutative group with injective
doubling, that a quartic single-repeat fibre has at most floor(n/2) anchors.
In particular, the result applies to every odd cyclic group.

The family theorem assumes one residual pair B(a) per anchor a in R,
with a outside B(a) and 2g(a) + sum(g on B(a)) = x. It proves 2|R| <= n.
The fibre theorem chooses these pairs from the actual singleRepeatFibre
and concludes 2 * card(singleRepeatFibre g 2 x) <= n.

The residual graph has exactly |R| edges. Validity places every endpoint
outside R, makes every cycle odd, and forces any two cycles to share an
edge. The general graph counting theorem bounds edges by vertices in
the graph induced on the complement of R. Thus |R| <= n - |R|.

Both original proof bodies pass the original and supported Mathlib
revisions with five exact printed types, three unchanged definition
values and only standard axioms. Builds reuse selective caches with at
most four compiler threads. The argument is uniform in n and uses no
finite enumeration.

The two fibre statements and their four graph parity/counting prerequisites
are awaiting a combined six-node Prove2Me export. The fibre bound alone
does not establish repeated-sum growth or a full-rank coefficient
combination. Generic G1, G2 and G3 remain open.
