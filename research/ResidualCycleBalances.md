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
finite tuple or modulus enumeration is used. These two new proofs have
not yet been exported or uploaded to Prove2Me.

What remains is the interface from actual residual graph walks to these
coordinate encodings, followed by the graph decomposition and the
proposed bound 2|R|<=n. The global repeated-sum growth inequality, a
single full-rank coefficient combination, and G1/G2/G3 remain open.
