# Translated squarefree sum packing

Let g be a valid tuple in any additive commutative group and let S_k
be the set of values of sums over k distinct coordinates. If a shift t
is absent from S_k-S_k, then

    |(S_(k+1)+t) intersect S_(k+1)| <= binomial(2k+2,k+1).

In particular, if t is not a coordinate difference, two translates of
the squarefree pair-sum set meet in at most six points. The bound holds
for every n and needs neither cyclicity nor odd order.

The five Lean results prove the following steps:

1. A family of disjoint support pairs of sizes p and q, all with the same
   signed evaluation, has at most binomial(p+q,p) members.
2. A translated match of (k+1)-supports has disjoint sides when the shift
   is absent one degree lower: cancel any purported common coordinate.
3. The support matches therefore obey the support-binomial bound.
4. Every common value comes from a support match, giving the image bound.
5. Degree two specializes to the six-point intersection bound.

The counting proof reuses the existing uncrossing and separating-
permutation arguments. Distinct disjoint pairs with the same evaluation
have disjoint events of separating permutations. Each event occupies
exactly the reciprocal support-binomial fraction of all permutations.
The original theorem bodies of the reused helpers are preserved in the
small supported-revision build; compiler spans determine the extraction.

Both the original Mathlib revision 81a5d257c8e410db227a6665ed08f64fea08e997
and the supported revision 0df444a360eaa60ab8c11dca51a86af692955474 pass.
The audit compares twelve exact declaration types and two definition
values, with only the standard Lean axioms.

For quartic single-repeat sums, this controls collisions between anchors
a and b when 2(g_b-g_a) is not a coordinate difference. Those exceptional
anchor pairs still require a separate argument. The result does not
prove the absolute quartic bound, the central-degree bounds, or any of
G1/G2/G3. It is also distinct from the anchored-cube quarter bound, which
has counterexamples. The next task is to combine this uniform bound with
control of exceptional doubled differences.


## Verified Prove2Me packing chain

All five translated squarefree packing results are private and Proved.
Verified submissions and exact server proof-source readbacks pass.
Both revisions verify five original target types and dependency sets,
nine original helper types, and the validity and separating-permutation
definition values. Every original proof body is retained. One existing
proved interface is reused; no new definition bundle is required.
A single supporting root retains all five results.

The consolidated DAG has 1019 nodes and 2330 edges. All 697 exact proof dependency sets across 34 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The quartic application still needs control of anchor pairs whose doubled
difference is a coordinate difference. The absolute quartic and central
bounds and all generic gates remain open.

* equal_evaluation_disjoint_family_card_le_choose: 4aeabcaf-957a-4623-b972-4867b9019116
* translated_supports_disjoint_of_no_smaller_shift: d32a1d12-94bd-40c9-8095-7b7e33adbc61
* translated_squarefree_family_card_le_choose: 75692012-d877-4e43-bb82-f3ddc90df8fb
* translated_squarefree_intersection_card_le_choose: 10dbb8ef-17ea-4520-ba4e-1569b5dc2f3c
* translated_pair_sum_intersection_card_le_six: 35c743d6-9781-4921-821e-9b152bcd7ecc
