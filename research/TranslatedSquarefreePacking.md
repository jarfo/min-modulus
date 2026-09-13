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
