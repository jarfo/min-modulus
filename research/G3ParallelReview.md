# Parallel G3 review and continuation

The 13 September review fetched commit aa24045219473f620b0f63873f3103fe2a2045ca
from origin/prove2me-001. It is the only new commit beyond the common ancestor
and adds MinModulus/G3ExceptionalStructure.lean. There is no prove2me-001
branch in the UNIQUE remote. The parallel checkout is now at
../min-modulus-001, and its most recent substantive log entry is
2026-09-12T17:47:16.601Z.

## Verified parallel result

For n>=3, n not a power of two, L=floor(log2 n), and m=n-L-1,

    2 * globalBound(n-1) = 2^(L+1) * (2^m-1).

The odd factor is Mersenne. It divides the exceptional modulus, and no
valid n-tuple exists modulo that odd factor: the finite-abelian bound
would require 2^(n-1)<=2^m-1. The full source, including four arithmetic
helpers, compiles independently on Lean 4.32.0 and Lean 4.33.1. All eleven
checked declaration types and both definition values match, and only
standard axioms occur. The supported dependency port adds the exact
original globalBound definition; its value is included in that comparison.

Four existing private Prove2Me nodes were read back as Proved, with their
submissions ACCEPTED and their statements, preambles, descriptions and
supported Mathlib revision matching the parallel payloads. The server's
exact solution files also match the parallel checkout. No duplicate
statements or proofs are uploaded by this integration.

* log_pred_eq_log_of_not_pow: 6cfe0220-363f-4e4b-b4d2-a243b3034397
* exceptional_modulus_eq: 18dda2ab-98bf-49ed-97d6-89b31c9a58e1
* odd_part_dvd_exceptional: 1a5e142f-5f64-4991-b23a-2f138c1d581c
* not_validTuple_odd_part: d107e6af-acab-4bfe-b6e0-a785323117e9

## Comment 96b76a47

The live comment is 96b76a47-c0d5-4cd8-9a15-5ffb0c6e81ac, posted on
12 September at 17:47:02 UTC. Its factorization and odd-part obstruction
are verified as above. Its Chinese-remainder consequence is valid: a rival
modulo the odd factor that also matched modulo 2^(L+1) would be a rival
upstairs. Therefore any rival of a valid upstairs tuple has a nonzero
value in the kernel of projection to the odd factor. There are exactly
2^(L+1)-1 nonzero possible values, at most 2n-1.

The description of a chain of L+1 deletions is an explanation of the
remaining equality case, not a proved unconditional descent chain. It
uses the outstanding deletion/G2 machinery. If fewer deletions occurred
in such a chain, the terminal length would be larger than m, which G2
would already prohibit at modulus 2^m-1. Exactly one deletion per halving
is the case in which the numeric bounds have no remaining slack.

The proposed pigeonhole step is still open. It requires two distinct
witness coefficient vectors c,d with the same target and c-d>=-1 in every
coordinate. Equal targets alone do not imply that condition.

For subset-collision witnesses c=c(S1,T1), d=c(S2,T2), the exact conditions
for that subtraction are both

    T1 intersect S2 is contained in S1 union T2,
    |T2|-|S2| <= |T1|-|S1|+1.

The first is the tail condition cited in the comment. The second is the
anchor condition, since c(0)=|T1|-|S1|. The comment says the tail condition
is needed; it does not prove it sufficient or construct the required pair.

## Generic continuation

[G3WitnessCompatibility.lean](G3WitnessCompatibility.lean) makes the gap
precise for arbitrary tuple length and arbitrary additive abelian group.
For witnesses whose tail coefficients lie in {-1,0,1}, c-d has floor -1
if and only if d(0)<=c(0)+1 and no tail index has c=-1,d=1.

Consequently distinct witnesses at the same target, with an admissible
anchor difference, must have such an opposite-sign tail coordinate.
A fixed target and the set of omitted tail coordinates determine a
light witness uniquely: with equal omitted sets, choose the subtraction
direction having nonnegative anchor. This also bounds any finite family
at one target by 2^(n-1).

These four new generic theorems pass both revisions, with six exact type
and axiom checks and both defining predicates matched. They provide a
compatibility interface and a counting restriction, not the missing
compatible-pair existence argument. G1, G2, G3 and the main arbitrary-n
conjecture remain open. No new finite exclusion search or mod-120 upload
is started.
