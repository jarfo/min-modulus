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

The split export passes both revisions: seven exact original target
types and dependency sets, two external interface types and three existing
definition values match. Exact parser spans retain every original proof
body. No new definition bundle or inline helper is required. Metadata and
live preflight pass; private publication is pending. Two supporting roots
retain the certificate floor and the counterexample quartic consequence.
