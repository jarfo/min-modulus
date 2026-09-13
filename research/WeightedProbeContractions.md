# Weighted probes factor through matrix contractions

[WeightedProbeContractions.lean](WeightedProbeContractions.lean) separates
the full weighted probe into two exact operations, uniformly in the tuple
size and the coefficient degree.

For a residual support S and a matrix row a, define

    C_M(a,S;f) = sum_(b not in S) M[a,b] f(S union {b}).

The degree-(d+1) weighted probe then satisfies

    P_M(y;f) = sum_(a,S: |S|=d, 2*g_a+sum_S g=y) C_M(a,S;f).

The first theorem reindexes the original support T by S=T without b.
The second distributes the matrix weights and exchanges the finite sums,
giving this factorization. The third shows that zero contractions give
zero weighted probes at every residue.

The fourth theorem proves that an injective matrix action on coefficient
vectors preserves every positive-degree squarefree coefficient through
the contraction stage. For a support T, choose b in T and put S=T without
b. For fixed S, the contractions are M applied to the vector whose c-th
entry is f(S union {c}) when c is outside S, and zero otherwise. Matrix
injectivity recovers that vector, including its b-th entry f(T).

All statements hold over arbitrary coefficient semirings. The factorization
requires no validity or odd-order hypothesis, and the contraction recovery
theorem does not involve the tuple or cyclic group at all.

This identifies the remaining full-matrix problem precisely: residue
grouping, followed by restriction to outputs outside the doubled coin
cover, must preserve the image of the contraction map for some M.
Matrix injectivity alone does not prove this. In particular, the identity
matrix is injective, but the verified diagonal obstruction shows that
subsequent grouping and restriction can still lose coefficients.
The central repeated-sum bounds and generic G1/G2/G3 remain open.

Local verification and platform publication status are recorded below.

Four original proof bodies and the contraction definition pass Lean 4.32
and 4.33.1. Seven exact declaration types, three definition values and
standard-axiom audits match. All four statements and the contraction definition are now published on Prove2Me.

## Matching alone does not establish weighted rank

A separate exact symbolic calculation checks the matrix

    [ a  c  0  0 ]
    [ 0  b  d  0 ]
    [ 0  0  c  a ]
    [ b  0  0  d ]

Its determinant is identically zero, while its leading three-by-three
minor is a*b*c. Thus its rank over Q(a,b,c,d) is three. The vector
(-c*d, a*d, -a*b, b*c) is a nonzero symbolic kernel vector.

Each coefficient matrix of a,b,c,d is a partial permutation matrix.
The coefficient matrices have zero joint kernel and cokernel, and the
union of their supports has a perfect matching (the diagonal). These
facts still do not yield one injective weighted combination: the two
perfect matchings contribute the same monomial with opposite signs.

This is an abstract matrix-space example, not a realization of the full
probe family of a valid tuple and not a min-modulus counterexample.
The calculation uses exact polynomial arithmetic, separately from the
four Lean proofs above, with no tuple or modulus enumeration. A rank
argument must use more of validity's relations between different probe
labels than this matching information alone.


## Verified Prove2Me contraction chain

All four contraction results are private and Proved, and the new
definition is published privately. Verified submissions and exact
server proof-source readbacks pass. Both revisions verify four original types
and dependency sets, three definition values, and all original proof
bodies. No inline helpers or external theorem interfaces are needed.
Two supporting roots retain the entire chain.

The consolidated DAG has 1010 nodes and 2312 edges. All 692 exact proof dependency sets across 33 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The unresolved rank step is preservation of the contraction image through
residue grouping and restriction outside the doubled coin cover, for one
full matrix. Matrix injectivity alone does not imply this. Central
repeated-sum bounds and all generic gates remain open.

* single_repeat_probe_reindex_residual_support: 7ea0495f-552a-4bfd-8cb4-7389be18b21c
* weighted_probe_eq_grouped_contractions: 327a5184-b093-45fd-9dad-d16c15fb4719
* weighted_probe_eq_zero_of_contractions_eq_zero: 07600286-2cf2-4b81-aae5-327c5249b017
* injective_matrix_contractions_determine_coefficients: 2ece6d40-9960-4c1e-8064-e4676edb55aa
