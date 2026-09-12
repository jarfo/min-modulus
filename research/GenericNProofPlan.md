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
