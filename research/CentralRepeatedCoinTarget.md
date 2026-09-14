# CR1 — absolute central repeated-cover inequality

Status: **unproved research target**. This is a proposed sufficient
strengthening of G2, not a proved theorem or an established consequence of
the min-modulus conjecture.

Let N be a positive odd integer and let g:Fin n -> ZMod N be valid: the
all-ones multiplicity vector is the unique nonnegative multiplicity vector
of total weight n with weighted sum equal to sum_i g_i. Let D_k be the set
of residues admitting a degree-k representation with a repeated coordinate.
The proposed target is, for k>=4 with k=floor(n/2) or k=ceil(n/2),

    |D_k|+1 >= sum_(j=0,...,k-1) choose(n,j).

The quantifiers range over all n, all positive odd moduli and all valid
tuples. No affine doubling closure, density, layer-overlap cap or restricted
multiplicity pattern is assumed.

[AbsoluteRepeatedCoinBounds.lean](AbsoluteRepeatedCoinBounds.lean) already
proves that exactly this uniform hypothesis implies OddStratumLowerBound.
The published sufficiency theorem is
`MinModulus.Research.oddStratumLowerBound_of_balanced_repeated_bounds`
(Prove2Me ID `1971fd39-22d6-4f56-acbb-64fa3209b49f`). The new statement's
entire quantified type is checked by Lean to match that theorem's explicit
hypothesis. The lower-degree base cases are already included in that proof.

[ClosedDoublingCoinCountsResearch.md](ClosedDoublingCoinCountsResearch.md)
and [MersenneExactCoinCountsResearch.md](MersenneExactCoinCountsResearch.md)
prove equality in the affine-doubling-closed class and in every Mersenne
power tuple. [CentralLayerOverlapResearch.md](CentralLayerOverlapResearch.md)
shows exponential overlap even in that sharp family. Thus a proof of CR1
must count the full repeated union and accommodate large overlaps.

The draft statement is checked on both the original Mathlib revision
81a5d257c8e410db227a6665ed08f64fea08e997 and the supported revision
0df444a360eaa60ab8c11dca51a86af692955474. Its statement file ends with the
platform's expected `by sorry` placeholder. This is a type check, **not a
proof**. No solution for CR1 is being submitted.

CR1 is now private and Open on Prove2Me. The statement readback and
mission linkage are verified. No CR1 proof has been submitted. The three
main gates G1/P6, G2/From7 and G3/From7 remain open. CR1 is an additional
research target, not a replacement for those gates or for alternative
proof routes.

CR1 is private and Open on Prove2Me, with an exact statement readback and
an attached research milestone. No CR1 solution has been submitted.
Theorem ID: 06a6b75d-6df1-4976-ae05-72ff1e7fc854
Milestone ID: 500f994a-6a1e-4cd4-8aa1-e183f116b1f9

The consolidated DAG has 1289 nodes and 2954 edges. All 840 exact proof dependency sets across 61 bundles match. G1/P6, G2/From7, G3/From7 and CR1 remain open. Its four open leaves are the three core gates and CR1.

[OutsideCubeRepeatedBoundsResearch.md](OutsideCubeRepeatedBoundsResearch.md) now proves that the repeated-cover bound for g is equivalent, at every anchor q, to |C_k(g-g_q) outside B|+1>=sum_(j<k) choose(n-1,j), where B is the entire anchored subset-sum cube. The proof retains all Pascal boundary terms and translation invariance. This is an equivalence only; the central outside-cube inequality remains unproved.
