# Counterexample growth constraints and certificate limits

Seven generic results record a restriction on the numerical certificate
method and a necessary growth condition inside any large odd counterexample.

If rank two is permitted at support size 2*k with k>=3, the fractional
certificate objective is at least 6*choose(2*k-4,k-2), hence at least
three eighths of choose(2*k,k). This is a limitation of the relaxation;
no realization of its abstract profile by a valid tuple is asserted.

For any valid odd-modulus tuple with n>=144 and N<2^n-1, the dense-case
obstruction forces (n-9)*|E|<=(n-12)*choose(n,2), where E consists of
anchor pairs with disjoint coordinate representations of their doubled
differences. The earlier quadratic-count theorem then yields

    |repeatedCoinCover(g,4)| >= choose(n+1,2)+choose(n,3).

The counterexample premise remains explicit. This quartic consequence
does not establish the higher central-degree inequalities; generic
G1/G2/G3 remain open. The original proofs are in
TranslationRankCertificateBarrier.lean and OddCounterexampleQuarticBound.lean.

All seven results are private and Proved on Prove2Me. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify seven original target types and dependency sets, two external
interface types and three existing definition values. All original proof
bodies are retained. No new definition bundle or inline helper is needed.
Two supporting roots retain the certificate floor and the hypothetical
counterexample quartic-growth consequence.

The consolidated DAG has 1231 nodes and 2816 edges. All 808 exact proof dependency sets across 54 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The numerical certificate premises remain explicit. Sufficient central-degree estimates and unrestricted G1/G2/G3 remain open.

* rank_certificate_objective_ge_single_rank: e14231c2-cd66-477d-94d4-74f7c3be1825
* central_choose_le_sixteen_two_steps: ec492dfc-5e31-4bbc-9124-148e47a9b542
* rank_two_translation_certificate_lower_bound: d3c37900-4334-48fa-b9bc-ac7f3ab668d2
* rank_two_translation_certificate_central_fraction_lower_bound: a29539e7-4c53-4a27-b9dd-b67d4d42a94d
* disjoint_doubled_difference_pair_complement_data: db68459a-ecc5-4280-a72e-999049ef4a41
* disjoint_doubled_difference_sparsity_of_odd_counterexample: 4a106221-3692-4e86-a082-ea02f484f946
* absolute_quartic_bound_of_large_odd_counterexample: ec1720f8-73fd-423d-beba-cc8198d5a591
