# Cyclic fixed points and negative affine closure

Four Lean results remove the fixed-point term from the preceding
negative affine domain bound.

For any valid tuple g at any nonzero cyclic modulus N, and any t, at
most two coordinates satisfy

    3*g_i=t.

No oddness or invertibility of three is assumed. For a coordinate in
this fibre, let q_i=floor(3*val(g_i)/N). Least representatives give

    3*val(g_i)=val(t)+N*q_i,    q_i in {0,1,2}.

Distinct fibre coordinates have distinct quotient labels. If three
existed, their labels would be 0,1,2 in some order. Adding the two
extreme representative equations and doubling the middle one produces
an arithmetic progression among three distinct coordinates, contradicting
pair-sum rigidity. Cancellation of three occurs in natural representatives,
so moduli divisible by three are included.

Now suppose g(f(i))+2*g_i=t on a finite domain S. Fixed points of f lie
in the triple fibre, hence there are at most two. Combining this with
the verified negative affine domain bound gives, whenever doubling is
injective,

    2*|S| <= n+2.

At odd modulus doubling is injective. A negative affine map closed on
the entire tuple would therefore imply n<=2. Thus such full negative
closure cannot occur for a valid tuple of dimension at least three.

These are structural restrictions. They do not extract an affine block
from dense represented doubled differences. The positive affine case,
the remaining quartic density argument, absolute central inequalities
and generic G1/G2/G3 remain open. Positive one-escape doubling already
has a separate proved theorem and is not reproved here.

All four original proofs pass both Mathlib revisions. Eight exact
declaration types and the ValidTuple definition value agree. The axiom
audit finds only standard Lean axioms. No new definition is introduced.
Split Prove2Me export and publication remain.

## Verified four-theorem cyclic fixed-point export

All four cyclic fixed-point statements and original proof bodies have
a verified split export on both revisions. Four exact target types and
dependency sets, three external interface types and the ValidTuple
definition value agree. No inline helper or new definition bundle is
introduced. Metadata and live preflight pass; publication is pending.
The affine-domain and full-closure hypotheses remain explicit. Extracting
structure from pair density, absolute central inequalities and generic
G1/G2/G3 remain open.
