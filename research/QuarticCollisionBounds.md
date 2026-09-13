# Quartic collision bounds and an explicit sparsity criterion

Let g be a valid tuple of n coordinates. Write R_2(x) for the anchors
of pure quartic representations x=2*g_a+g_i+g_j, where a,i,j are distinct.
Let B=binomial(n,2), and let C be the number of unordered anchor pairs
{a,b} for which

    2*(g_a-g_b)=g_p-g_q

for two distinct coordinates p,q outside {a,b}. The definition
`disjointDoubledDifferencePairs` records precisely these pairs; the
orientation is existential, so each unordered pair is counted once.

Six theorems connect the existing incidence identity to a quantitative
quartic lower bound.

* If a doubled anchor difference has no coordinate representation, at
  most six selected values belong to both anchor fibres. This holds in
  every additive commutative group.
* If the difference is represented by g_p-g_q, injective doubling gives
  at most n-3 common values when both endpoints avoid the anchors, and
  zero otherwise. The proof uses the intersection on the n-2 remaining
  coordinates, rather than the larger unrestricted intersection.
* Consequently, exceptional anchor pairs have cap n-3; all other pairs
  have cap six.
* Summing the exact unordered-pair collision identity gives, for n>=9,

      sum_(x in Y) binomial(|R_2(x)|,2) <= 6*B+(n-9)*C.

  Here Y is any selected value set, and doubling is assumed injective.
* At odd modulus and n>=14, the explicit sparsity hypothesis

      3*(n-9)*C <= 2*(n-14)*B

  implies at least binomial(n,3) quartic repeated values outside the
  doubled two-coin cover. This follows by combining the collision bound
  with the proved incidence supply (n-4)*B and the identity
  3*binomial(n,3)=(n-2)*B.
* Adding the exact doubled two-coin baseline yields

      |D_4| >= binomial(n+1,2)+binomial(n,3).

The sparsity hypothesis is not asserted for arbitrary valid tuples.
Dense exceptional cases remain open. This is a quartic result; the
absolute central inequalities required for generic G2 remain open,
along with G1 and G3.

All six original proofs pass on Lean 4.32 / Mathlib
81a5d257c8e410db227a6665ed08f64fea08e997 and Lean 4.33.1 / Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. Seventeen exact declaration types
and five definition values agree. The compiler axiom audit finds only
standard Lean axioms. Builds reuse cached dependencies and use at most
four compiler threads. All six results and the new definition are now verified privately on
Prove2Me and integrated into the consolidated DAG.


## Verified Prove2Me quartic collision chain

All six quartic collision results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify six original target types and dependency sets, eight
external interface types, two original inline helper types and five
definition values. Every original proof body is retained. One new
definition records exceptional unordered anchor pairs. One supporting
root retains the complete six-theorem chain.

The consolidated DAG has 1082 nodes and 2478 edges. All 729 exact proof dependency sets across 39 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The conditional quartic bound is proved. Dense exceptional cases, the
higher absolute central inequalities and generic G1/G2/G3 remain open.

* quartic_pair_values_card_le_six_of_no_coordinate_difference: 62a8c460-e4ab-4ac1-b883-0bd9c061c581
* quartic_pair_values_card_le_of_coordinate_difference: c53a2dd4-b99c-4d69-8b77-980759257598
* quartic_anchor_pair_values_card_le_exceptional: d2e8183c-6402-441a-97fa-2641bef143de
* quartic_pair_collision_sum_le: c170dd60-ac6d-4518-9f2c-19a96b606d3f
* quartic_outside_doubled_cover_card_of_sparse_differences: 6536bb34-c9fc-4132-9bc2-d5dca22bb81d
* absolute_quartic_bound_of_sparse_differences: 1c1ef1be-fd69-4fd0-8485-15408fce294d
