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
standard-axiom audits match. Platform export and upload remain.
