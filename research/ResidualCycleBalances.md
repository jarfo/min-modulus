# Translating residual cycles into multiset balances

[ResidualCycleBalances.lean](ResidualCycleBalances.lean) supplies two
cycle translations for the quartic residual-fibre argument. The cycles
are encoded by finite coordinate maps and explicit endpoint equations;
this file does not yet define the residual SimpleGraph or count its edges.

The first theorem excludes every nonempty alternating even residual
cycle, and more generally a union of such alternating cycles. For a
positive m, take distinct anchors a_i and b_i, with the two anchor images
disjoint. Suppose their residual edges are

    B_(a_i) = [u_i,v_i],     B_(b_i) = [v_i,u_(sigma i)],

where sigma permutes Fin m. Assume these anchors lie in one quartic fibre
of a valid tuple in an abelian group with injective doubling. Reindexing
the residual multiset sums by sigma makes the aggregate on the a anchors
equal the aggregate on the b anchors. The proved residual-trade rigidity
then identifies the two disjoint nonempty anchor sets, a contradiction.
No assumption that the residual vertices are distinct is needed.

The second theorem translates an odd cycle with 2m+1 edges into a rooted
balance. Use m+1 distinct positive anchors a and m distinct negative
anchors b, and endpoint equations

    B_(a_i) = [u_i,v_i]           for i<m,
    B_(b_i) = [v_i,u_(i+1)]       for i<m,
    B_(a_m) = [u_m,u_0].

Then the aggregate positive residual multiset equals the aggregate
negative residual multiset plus [u_0,u_0]. This is a combinatorial
identity; it requires no valid tuple or group hypotheses. The previous
rooted-balance theorem can be applied when the root lies outside the
anchor family and a second such balance has disjoint anchor support.

The code uses explicit multiset multiplicities, finite sums and
permutation reindexing. Both proofs pass the original and supported
Mathlib revisions, with three exact printed types, the ValidTuple
definition value, standard axioms, and identical source bodies. No
finite tuple or modulus enumeration is used. Both statements are now Proved on Prove2Me; see below.

What remains is the interface from actual residual graph walks to these
coordinate encodings, followed by the graph decomposition and the
proposed bound 2|R|<=n. The global repeated-sum growth inequality, a
single full-rank coefficient combination, and G1/G2/G3 remain open.

## Verified statement/proof export

Both residual-cycle translations pass both revisions as separate statement
and proof files. Their two original types and two exact theorem
dependency sets match, as does ValidTuple in type and definition value.
There are no proof holes outside declared interfaces. The export
reuses one Proved theorem interface and existing definitions; it adds
no definitions or inline helpers. Both split proof bodies match the
checked source file. Metadata, exact live readbacks and unused names
pass. Both theorem nodes are now Proved on Prove2Me. The graph
walk interface, counting consequence and G1/G2/G3 remain open.

## Verified Prove2Me proofs

Both residual-cycle statements are private and Proved, with verified
submissions and exact server proof-source readbacks. Both independent
supporting roots retain the even-cycle exclusion and odd-cycle balance
theorems. Existing definitions are reused.

The consolidated DAG has 936 nodes and 2158 edges. All 651 proof dependency sets across 24 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

* no_even_residual_cycle: 7dc91880-097b-4c1e-95da-6d8845999dfd
* odd_residual_cycle_balance: fe539253-cd25-4e1c-98d0-ab80bb5031f5
