# Two escapes from every outside quadratic translate

The existing `MinModulus.AlmostDoubling` theorem already proves the sharp
odd bound for every valid tuple with at most one affine-doubling escape.
The new transfer connects that theorem to the quadratic translate method.

For n>=5, let t lie outside the coordinate set A, and suppose at least
n-1 coordinates satisfy g_i+t in C_2. The quadratic rigidity lemma makes
all these hits doubles, because there are at least four hits. Choose an
index f(i) with g_i+t=2*g_f(i). Validity makes this partial map injective:
two equal chosen indices would give equal original coordinates.

Its image therefore misses at most one coordinate. Reversing the matched
pairs gives an index a such that

    for every i != a, some j satisfies g_j = 2*g_i - t.

This transfer does not require oddness. The existing odd one-escape
bound then proves N>=2^n-1. Consequently any hypothetical odd
counterexample has at least two distinct escapes from EVERY outside
quadratic translate. This strengthens the earlier one-escape condition.
It does not assert existence of a translate with n-1 hits and does not
prove the remaining generic repeated-sum growth inequality.

`QuadraticOneEscapeTransfer.lean` contains three lemmas: extraction of
an exception from a large finite index set, the reverse matching above,
and two quadratic escapes from exclusion of one-escape affine closure.
These pass both Lean revisions with exact types and definition values.
The final lemma keeps the affine-closure exclusion as an explicit premise.

`QuadraticOneEscapeBound.lean` applies the existing unconditional
`odd_lower_bound_of_valid_one_escape_doubling` theorem to discharge that
premise under N<2^n-1. Its two resulting theorems now pass BOTH revisions,
including the full one-escape proof dependency port and standard-axiom
audits. The later platform export is accepted; its details appear below.

The compiler identifies 440 project constants, including generated proof
helpers, owned by 122 named source declarations in 26 modules. Extracting
those exact declaration commands avoids the 1025-module source import
closure. Retained variable context contributes one additional module
import. Three simp calls in two AlmostDoubling proofs explicitly unfold
Equiv.ofBijective for compatibility; all other selected declaration
bodies are unchanged. All 122 original statement types and 13 definition values are checked: 121
types match literally; the remaining type differs only in the printed
setOf/Set.ofPred name and its original statement passes the Lean kernel. The two new
quadratic applications also have exactly their original types. This is an isolated supported build of the required proof; the
main repository's complete import graph is not changed.

The one-escape affine-doubling bound is an existing result, not a new
proof of G2. The new contribution is its conversion into a stronger
quadratic-translate restriction. All three generic gates remain open.

## Accepted Prove2Me statements

Twelve theorem statements are now private and Proved, with ACCEPTED
submissions and exact server proof-source readbacks. Six fill the existing
one-escape affine-doubling chain; one specializes the accepted general
translate theorem to quadratic hits; three transfer lemmas and two
applications establish the uniform two-escape restriction. The export
reuses eleven existing theorem interfaces and adds one lightweight
quadratic-hit definition. Both Lean revisions, exact original types,
eleven definition values and every proof dependency set pass.

* logarithmic_chain_of_valid_affine_cycle_chain: 1c92f847-7ce6-4359-8227-6aae177e421b
* stratum_lower_bound_of_valid_affine_cycle_chain: 9dc3d0f8-82d5-4a5f-9970-74386d2299b2
* valid_fixed_of_valid_doubling_chain: 9c78557d-f3e6-4f4b-9882-73eb418e9f04
* stratum_lower_bound_of_valid_almost_doubling_perm: 5d5daecd-492e-4bed-bd7b-947165bf0956
* stratum_lower_bound_of_valid_one_escape_doubling: 45702a98-bc92-4647-b7d3-147734a7443f
* odd_lower_bound_of_valid_one_escape_doubling: fae81b54-b0bd-4ed1-8d1f-14843d6a274e
* quadratic_translate_hit_is_double_of_four_hits: 17ddbb91-53d8-402a-8722-2d4af434d3f8
* exists_exception_of_large_index_set: 54dd4b58-e5ee-4536-8569-dd9ea33e883d
* one_escape_of_large_quadratic_translate: 28687d38-48f0-47a4-a900-5ac4f28c30de
* two_quadratic_escapes_of_one_escape_exclusion: 96d38f36-efbb-4b95-9083-0f64e88d7da6
* odd_lower_bound_of_almost_full_quadratic_translate: 833273ea-ecce-4feb-820c-6d201a5f492b
* two_quadratic_escapes_of_odd_counterexample: a064ccd1-c7ce-4fa9-a202-43f8e996d884

Two terminal supporting roots connect these results to the consolidated
DAG, now 900 nodes and 2072 edges. All 633 proof
dependency sets across 18 bundles match. The three generic open leaves
are unchanged. The full repeated-sum growth inequality is still open.
