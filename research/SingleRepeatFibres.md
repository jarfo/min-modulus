# Single-repeat collisions in the generic proof

The main objective remains the min-modulus conjecture for arbitrary n.
This result controls collisions uniformly in both n and the coin degree;
it does not discharge general G2, G1 or G3.

Let g be a valid n-tuple in an abelian group with injective doubling
(in particular, in ZMod N for odd N). Fix a degree d=k+2 and a residue x.
A single-repeat representation has the form

    x = sum_{i in S_a} g_i + g_a,
    |S_a| = k+1, a in S_a.

Thus a occurs twice and the other k coordinates occur once. Let R_x be
the set of possible repeated coordinates, and write r_x=|R_x|.

[SingleRepeatFibres.lean](SingleRepeatFibres.lean) proves

    r_x <= binomial(n-r_x,k).

This is a theorem for every n and k, without a half-degree restriction or
a small-modulus hypothesis. More generally the same bound applies to any
selected family of such representations indexed by distinct anchors.

## Proof and global count

If distinct anchors a,b represent x, then b cannot belong to S_a.
Otherwise cancelling g_b makes the squarefree sum on S_b equal a multiset
with two copies of a. Validity prohibits that replacement. Therefore
S_a intersects R_x in exactly {a}.

The residual sets B_a=S_a without a all have size k and lie outside R_x.
They are distinct: equality B_a=B_b and equality of represented values
imply 2g_a=2g_b, so injective doubling and validity give a=b. These residual
sets inject R_x into the k-subsets of its complement, proving the bound.

For each anchor and value, validity also makes the support S_a unique.
Counting configurations first by support and then by value gives exactly

    sum_x r_x = (k+1) * binomial(n,k+1).

Define the explicit capacity

    q(n,k) = max {r in {0,...,n}: r <= binomial(n-r,k)}.

Every occupied fibre lies in D_(k+2), the set of repeated coin sums.
The formal global consequence is

    (k+1) * binomial(n,k+1) <= q(n,k) * |D_(k+2)|.

All fourteen declarations compile on Lean 4.32.0 and Lean 4.33.1 with
supported Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Twenty
literal declaration types and standard-axiom audits, and nine definition
values, match across revisions. The Lean proofs use no finite tuple or
modulus enumeration. Cached, previously audited dependencies are reused;
this is a module build, not a full clean rebuild of the project.

## What remains for arbitrary n

The global inequality above is weaker than the required growth

    |D_d| >= |C_(d-1)|  for d>=4 and 2d<=n+1.

For example, n=8,d=4 gives q(8,2)=4 and only |D_4|>=42 from this argument,
whereas the already proved cubic bound is |C_3|>=92. The new lemma controls
one class of collisions, but does not yet count enough different values.
Counting other repetition patterns together, or proving a suitable global
independence statement, remains necessary. Merely guaranteeing an escape
for each coordinate pair does not address this gap.

A constant collision cap would be false. The saved valid nine-tuple

    (0,1,130319,19,130283,361,129599,6859,116603) modulo 130321

has four single-repeat quartic representations of zero. They are
2a+0+(-2a)=0 for a=1,19,361,6859. Degree four is in the half-degree range
for n=9. A reproducible finite verifier checks all nine-coin multisets for
validity and all four representations. This refutes the proposed cap of
three, not the growth inequality or G2. No Lean proof of this finite
counterexample or of an unbounded family is claimed here.

The archive also reproduces the earlier check of 205736 residue fibres
from 3748 dimension/degree cases on 771 saved valid tuples. Those checks
are supporting evidence; the arbitrary-n fibre and incidence results
come from the Lean proof above. No new finite exclusion campaign is run.
