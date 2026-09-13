# Generic-n proof priority

The objective is the min-modulus conjecture for arbitrary n. Finite
dimensions are supporting results. The local seventh odd dimension is
complete, so local general G2 is equivalent to its restriction to n>=8.
The Prove2Me G2 frontier remains From7 until its connecting proofs are
accepted. General G1 and G3 also remain necessary and unresolved.

The current generic G2 target is the following. For a valid tuple
g:Fin n -> ZMod N with N odd, let A be its coordinate set, C_d the set of
all d-coin sums with repetitions allowed, and D_d the sums admitting a
repeated coordinate. Write 2·A for the dilate {2a:a in A}.

For every d>=2, Lean proves the exact identity

    D_d = 2·A + C_(d-2).

Validity gives a disjoint split into binomial(n,d) squarefree sums and D_d.
Consequently the desired increment is equivalent to

    |2·A + C_(d-2)| >= |C_(d-1)|.

The degree-two and degree-three increments are already proved uniformly.
The remaining hypothesis is the displayed inequality for d>=4 and
2d<=n+1. Its first open case is |2·A+C_2|>=|C_3| for n>=7. Proving just
that first case would not prove general G2: all required degrees matter.

[RepeatedCoinGrowth.lean](RepeatedCoinGrowth.lean) proves the exact
reformulation, the two base increments and the implication from the
remaining uniform inequality to full G2. It also proves that any odd G2
counterexample must exhibit a strict failure of that inequality at some
degree d>=4 in the half-degree range. This allows future arguments to
work within a hypothetical counterexample, where N<2^n-1 is available.
The cardinal inequality itself is not proved.

This route does not discharge G1 (the general primitive deletion step)
or G3 (the general exceptional-lift obstruction). The maintained server
DAG retains those independent obligations. No higher-dimensional finite
enumeration is planned; next proof effort should use arbitrary n and d.

## New uniform restriction on a counterexample

[Quadratic translate rigidity](QuadraticTranslateRigidity.md) proves that
an outside shift with A+t contained in A+A forces a cover by doubles and
hence all the required growth inequalities. Thus an odd counterexample
has an escape from A+A for every outside shift. In particular, each
distinct coordinate pair has a repeated quartic value outside 2·C_2.
The remaining issue is enough independent values, not just one per pair.

The linked note records an exact finite matrix experiment supporting an
absolute quartic bound. Its general rank assertion is unproved, and the
whole range of degrees is still required for a generic-n G2 argument.

## Uniform collision count

[Single-repeat fibres](SingleRepeatFibres.md) now proves, for every n and
d=k+2, that r anchors representing one residue satisfy
r<=binomial(n-r,k). Residual supports avoid all anchors and are distinct
by injective doubling. The exact total incidence is
(k+1)*binomial(n,k+1), giving a global lower bound on repeated sums after
dividing by the maximum permitted fibre size. Both revisions verify the
argument. This remains weaker than |D_d|>=|C_(d-1)|; counting enough
independent values across repetition patterns is still unresolved.
A reproduced valid n=9 example rules out a uniform single-repeat cap of
three even inside the half-degree range. No finite exclusion is added.

## Parallel generic G3 route

[The parallel review](G3ParallelReview.md) verifies the exceptional-modulus
factorization into a power of two and a Mersenne odd factor, and the
impossibility of a valid full-length tuple in that odd factor. Four existing
Prove2Me proofs are integrated into the consolidated DAG. The generic
continuation [G3WitnessCompatibility.lean](G3WitnessCompatibility.lean)
proves the exact subtraction-floor test, the forced reverse tail crossing,
and uniqueness from target plus omitted tail. The missing step remains
existence of two distinct compatible witnesses at one kernel target.
These supporting results do not discharge G3 or the other main gates.

## Reversible G3 kernel witnesses

[G3BalancedKernel](G3BalancedKernel.md) strengthens the generic quotient
argument: (n+1)q<2^n forces an equal-rank subset collision modulo the
Mersenne odd factor. Every hypothetical exceptional tuple therefore has
a nonzero kernel witness with all coefficients in {-1,0,1}, and its
negative is also a witness. At each target, such witnesses form an
antichain through their negative supports, giving the middle-binomial
Sperner bound. Eight theorems pass both revisions. The distinct compatible
same-target pair, and all three main gates, remain open.

## Kernel-witness avoidance at every coordinate

[G3MiddleLayer](G3MiddleLayer.md) proves, for arbitrary n>=3, that the
middle rank on n-1 coordinates exceeds the Mersenne odd factor. Every
hypothetical exceptional tuple therefore has a reversible kernel witness
vanishing at any chosen coordinate. Five theorems pass both revisions.
The kernel target may vary with the coordinate, so this does not supply
same-target compatible witnesses or discharge G3.

## Parallel G1 two-escape proposal

[The parallel review](G1TwoEscapeShiftReview.md) integrates the sufficient
implication TwoEscapeShift -> G1 from branch commit 285a7b97. The extraction
predicate remains unproved and is stronger than the current G1 input.
The original revision and standard axioms are checked; no supported port
or platform upload is claimed. The documentation limits the small-case
numerics and distinguishes the stratum endpoint from the global bound.

The four reusable G3 balanced-kernel statements are now accepted on
Prove2Me and connected through two supporting roots. The consolidated
DAG has 862 nodes; its three generic open leaves are unchanged.
