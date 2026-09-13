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
All four results are now verified on Prove2Me, reusing the fully proved
all-degree recurrence chain.


## Verified Prove2Me fibre transport chain

All four all-degree fibre transport results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, four
external interface types, two original inline helper types and two
definition values. Every original proof body is retained. Four existing
proved interfaces are reused; no new definition bundle is introduced.
One supporting root retains the entire four-theorem chain.

The consolidated DAG has 1059 nodes and 2424 edges. All 717 exact proof dependency sets across 37 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The fibre bounds are proved. Turning these collision restrictions into
enough distinct repeated values, the absolute central inequalities and
generic G1/G2/G3 remain open.

* doubled_difference_endpoints_mem_residual_union: 6a0de2fe-3f64-4d0b-8b03-7cec9e18bc31
* single_repeat_fibre_doubled_difference_endpoints_outside: 0a2c516c-6096-4684-ab95-2a540c7fc014
* single_repeat_fibre_coordinate_difference_edges_card_le: ffcad971-d1d0-4d6d-a65f-39a7a5e17663
* single_repeat_fibre_card_le_complement_of_all_differences: 5e484cbb-1a08-4561-83dd-edc68d295043
