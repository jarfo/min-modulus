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

Both results are private and Proved on Prove2Me. Verified submissions
and exact server proof-source readbacks pass. Both revisions verify two
original target types and dependency sets, four external theorem interfaces
and six existing definition values. Exact parser spans retain both
original proof bodies. No inline helper or new definition is required.
One supporting root retains the valid central-degree family and its
generic independent-block construction.

The consolidated DAG has 1245 nodes and 2847 edges. All 817 exact proof dependency sets across 56 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The central-degree union lower bounds and generic G1/G2/G3 remain open.

* independent_doubling_rectangles_force_many_layers: 6e1efd07-f859-412d-b0f4-91c524eda318
* mersenne_central_degree_exponential_layer_overlap: 867b1e8f-acbe-40eb-afb6-f277c09a4c2d
