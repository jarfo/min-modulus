# Doubled differences inside a single-repeat fibre

Let g be valid in an additive commutative group. Let R be an anchor set
and B_a a k-element residual support for every a in R, with a outside B_a
and all values 2*g_a+sum(B_a) equal. The residual degree k is arbitrary.

If a,b belong to R and

    2*(g_a-g_b) = g_p-g_q,   p != q,

then both p and q lie outside the entire anchor family R. The existing
single-repeat exclusion lemma makes every B_a disjoint from R; the new
all-degree coordinate-difference classification places p,q in B_a union
B_b. This implication needs no injectivity of doubling.

When doubling is injective, coordinate representations of doubled
differences give an injection from ordered distinct anchor pairs in R
to ordered distinct coordinate pairs outside R. Thus, if E is any family
of represented ordered pairs inside R,

    |E| <= (n-|R|)*(n-|R|-1).

The representation map is injective: equal image differences, injective
doubling and the existing uniqueness of nonzero differences identify the
original ordered anchor pair. Representing endpoints are automatically
distinct under these assumptions.

Consequently, if |R|>=2 and every pair of distinct anchors in R has its
doubled difference represented by coordinates, then

    |R| <= n-|R|.

This is a conditional half-fibre bound in every degree. The hypothesis
that every pair has a represented doubled difference is essential to the
stated corollary. The injection bound itself applies to any selected
family of represented pairs, even when other pairs are unrepresented.

Four original Lean proofs pass both Mathlib revisions. Nine exact types,
including the reused interfaces, and the ValidTuple definition value
agree; only standard Lean axioms occur. The difference-uniqueness proof
is reused from its existing source and verified supported cache. No
finite enumeration or default library build is added.

These results constrain how coordinate-difference collisions can occur
inside a whole fibre. They do not supply the global repeated-sum count
or the absolute central inequalities. Generic G1/G2/G3 remain open.
Prove2Me export and publication remain; the prerequisite all-degree
recurrence chain is currently being verified on the server.

## Verified four-theorem fibre transport export

All four fibre transport statements and original proof bodies have a
verified split export on both revisions. Exact target types, four
external interface types, two original inline helper types and dependency
sets agree. ValidTuple and the imported squarefreeTranslationMatches
definition values agree. No new definition bundle is introduced. Metadata
and live preflight pass; publication is pending. The final half-fibre
bound assumes every distinct anchor pair has a represented doubled
difference. The global count and generic G1/G2/G3 remain open.
