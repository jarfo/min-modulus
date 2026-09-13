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
audits. These applications have not been uploaded to Prove2Me.

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
