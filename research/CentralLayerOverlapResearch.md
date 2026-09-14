# Verified exponential central-layer overlap

Two generic results show that full squarefree-double layers can have
exponentially large overlap at a central-degree value. For every m>=1,
the valid Mersenne power tuple has n=6*m, N=2^(6*m)-1 and k=3*m.
Some x in D_k lies in at least 2^m distinct layers sum g(S)+2*C_m
with |S|=m. Here C_m includes all degree-m representations, and D_k
contains values with a repeated degree-k representation.

The first result constructs the overlap from an injective family of
four-coordinate blocks with two doubling identities per block. The
second realizes these blocks in the valid Mersenne family. Both are
symbolic proofs for arbitrary m. The modulus equals the conjectured
sharp odd bound, so this is not a counterexample to min-modulus.
Constant universal layer-multiplicity caps are impossible; weighted
or aggregate lower bounds on the entire union remain possible and open.
Generic central inequalities and G1/G2/G3 remain open.
The original proofs are in ManySquarefreeDoubleLayers.lean.

The split export passes both revisions: two exact original target
types and dependency sets, four external theorem interfaces and six
existing definition values match. Exact parser spans retain both original
proof bodies. No inline helper or new definition is required. Metadata
and live preflight pass; private publication is pending. One supporting
root retains the valid central-degree family and its generic construction.
