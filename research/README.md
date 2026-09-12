# Six-point obstruction to an unrestricted cubic interpolation bound

Let K have characteristic two and let w satisfy w²+w+1=0. The six points

```
(1,1,1), (1,w,1), (1,w+1,w+1),
(1,w+1,w), (1,w,w+1), (1,1,w)
```

are distinct and have no zero coordinates. For every homogeneous cubic f,

```
w * sum_i f(P_i) = coefficient of x*y*z in f.
```

The file proves this first for all ten cubic monomials, then for arbitrary
homogeneous cubics by linearity. It constructs the required w in
`GaloisField 2 2`, so the hypotheses are realized. The final theorem
`six_point_cubic_counterexample` combines the interpolation, distinctness,
nonzero coordinates and weight, and the inequality 6 < 2³−1.

This disproves the unrestricted claim that squarefree degree-n coefficient
extraction by distinct torus points with a common nonzero weight always
requires at least 2^n−1 points. The example leaves open the version restricted to the odd cyclic orbits
that arise from min-modulus characters. The example is not a
valid-tuple or odd cyclic-orbit counterexample. It does not settle G2 or
any other main research gate.

The standalone source lives at `research/CharTwoSixPointInterpolation.lean`
in the Lean repository. It is outside the default library and adds no
imports or build jobs to the main proof. From a built checkout, run:

```sh
lake env lean research/CharTwoSixPointInterpolation.lean
```

Verification on both revisions and the complete axiom/type records are
preserved in the [companion research archive](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/char-two-research).
The main conjecture and G1/G2/G3 remain open.

## Symmetric products and Frobenius

[SymmetricProductDependence.lean](SymmetricProductDependence.lean) proves
that the seven nonempty squarefree symmetric products for the valid tuple
(0,1,3,7) modulo 15 are dependent. Replacing the last product by the square
of the first gives seven independent vectors. Both revisions verify the
same twelve audited types with standard axioms. The
[companion archive](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/symmetric-product-research)
records the exact relation, the local repair, and bounded experiments on
the still-unproved Frobenius-span approach to G2. No default imports or
main research gates change.

## Anchored-cube intersection bounds

The [anchored-cube intersection certificate](AnchoredIntersectionCounterexample.lean)
refutes uniform pairwise-quarter and triple-eighth bounds for valid tuples
at odd modulus. For (0,11,8,6) modulo 15, the selected intersections have
five and three elements, exceeding four and two. The anchored union still
fills all fifteen residues. Both Lean revisions verify identical types
and standard axioms. Exhaustive tests cover dimensions 2–6 and odd moduli
through 63; some pair satisfies the quarter bound in every tested set,
but that weaker existence statement remains unproved.

## The surviving anchored-pair route

[AnchoredPairLowerBound.lean](AnchoredPairLowerBound.lean) proves that one
intersection of size at most `2^(n-2)` forces `N >= 3*2^(n-2)` for a valid
length-n tuple, n>=2. The small-pair inequality is an explicit hypothesis;
its existence at odd moduli remains unproved. Both Lean revisions pass,
with four literal type and standard-axiom comparisons. This standalone
file adds no default-library jobs.

Additional seeded tests sample 100,000 sets in each of dimensions seven
and eight, finding 426 and six valid sets respectively. Every valid sample
has some quarter-sized pair intersection. An independent Python checker
confirms all validity and intersection results. These samples are not
exhaustive; the small-pair existence claim remains open.
[Reproduction data](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-intersections-research/higher-dimensional-sampling).

## Adaptive anchored-union increments

[AnchoredIncrementObstruction.lean](AnchoredIncrementObstruction.lean) proves
that no anchor order for the canonical valid seven-tuple modulo 127 can
add at least 64,32,16,... new points successively. A qualifying pair covers
100 points, while every triple covers at most 115. The full union nevertheless
fills 127 residues, and the natural order meets the weaker cumulative targets.
Both Lean revisions pass all fifteen literal type and standard-axiom checks.
This eliminates the separate-increment strategy; the cumulative strategy
and the full G2 bound remain open. No default build jobs are added.
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-increment-research).

## Anchored-overlap multiplier relations

[AnchoredOverlapMultipliers.lean](AnchoredOverlapMultipliers.lean) proves that
nonzero overlap forces a ternary relation with anchor multiplier 2 through n.
It also proves that multiplier one is impossible, and that one relation-free
pair implies N >= 2^n - 1. Existence of that pair is an explicit hypothesis;
the general G2 theorem remains open. Both Lean revisions pass 18 literal
type and standard-axiom checks. The corrected parallel runs reproduce 605
relation-free ordered-pair occurrences, not the 632 claimed in their summary;
all intersections are {0}. The converse is false because the search omits
subset-cardinality constraints. No default build jobs are added.
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-multipliers-research).

## Cardinality-compatible anchored relations

[AnchoredCompatibleRelation.lean](AnchoredCompatibleRelation.lean) proves an
exact criterion for nonzero cube overlap: disjoint off-anchor signed supports
P,Q must admit a relation with 2 <= M, |Q| <= M and M+|P| <= n. Both directions
are proved by extracting subset supports and reconstructing subsets of the
required size. Absence of a compatible relation is equivalent to intersection
{0} and gives N >= 2^n-1. Existence of such a pair remains an explicit input.
Both Lean revisions pass ten literal type and standard-axiom checks. A related
binomial counting formula passes all 6,668 previously sampled ordered pairs;
the general formula is now proved in [AnchoredIntersectionCount.lean](AnchoredIntersectionCount.lean).
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-compatible-research).

## Exact anchored-intersection counts

[AnchoredIntersectionCount.lean](AnchoredIntersectionCount.lean) proves the
exact binomial-weight formula for every valid tuple. Normalized subset pairs
are in bijection with disjoint signed supports P,Q and a shared selector U;
for fixed |U|=r, the weight is binomial(n-|P|-|Q|,r), and the multiplier is
|Q|+r. The proof establishes both inverse maps and counts each fibre, so no
common point is counted twice. Identical source passes both Lean revisions
with all 28 literal type and standard-axiom audits. Bounding this sum for
suitable anchor pairs remains open; the identity alone does not prove G2.
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-intersection-count-research).

## Bounded multiplier packing

[AnchoredMultiplierPacking.lean](AnchoredMultiplierPacking.lean) proves
(r+1)*2^(n-2) <= N if one anchor pair excludes multipliers 2 through r.
Consequently every ordered anchor pair has a multiplier-two or multiplier-three
relation whenever N<2^n, including all possible G2 counterexamples. This
chooses a small witness; larger relations still contribute to intersections.
Excluding just multiplier two gives the three-quarter numerical bound.
Both revisions pass ten literal type and standard-axiom audits. Exhaustive
checks through dimension six and odd modulus 63 find a multiplier-two-free
pair in every one of 551,440 valid sets; general existence remains open.
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-multiplier-packing-research).

## Complementary coin intersections

[ComplementaryCoinIntersections.lean](ComplementaryCoinIntersections.lean)
proves that C_r intersect (sum(S)-C_s), for |S|=r+s, consists exactly of
r-subset sums of S and has binomial(r+s,r) elements. Thus
|C_r|+|C_s|<=N+binomial(r+s,r) whenever r+s<=n. Together with three-coin
counting, this gives N>=107 for every valid seven-tuple at odd order.
The ten odd moduli from 107 through 125 are now excluded by the
[completed seven-dimensional bridge](../MinModulus/G2OddSevenDimensions.lean). Identical source passes both revisions and all ten type/axiom audits.
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/complementary-coin-intersections-research).

## Half-degree coin growth and general G2

[HalfDegreeCoinGrowth.lean](HalfDegreeCoinGrowth.lean) proves that the growth
|C_k|+binomial(n,k+1)<=|C_(k+1)| for 1<=k and 2(k+1)<=n+1 would establish
the full odd-stratum bound N>=2^n-1 for every valid tuple. The proof combines
partial binomial sums with the exact complementary coin intersection bound.
The growth hypothesis remains explicit and unproved. Identical source passes
both Lean revisions, thirteen literal type/axiom audits and six definition-value
comparisons. This is a conditional research result, not a proof of G2.
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/half-degree-coin-growth-research).

## The proper-subset SDR fails at dimension seven

[AnchoredSDRCounterexample.lean](AnchoredSDRCounterexample.lean) proves full
validity of (0,41,97,107,110,215,251) modulo 329 and refutes the external-anchor
SDR proposal for its proper subsets. The six-element subsets omitting 110
and 251 both have only the value 51 available. This two-set obstruction is
inside the live dimension-seven-and-higher range. It does not refute G2.
Identical source passes both Lean revisions, nine literal type/axiom audits
and four definition-value comparisons. Independent checks of 427 sampled
valid seven-tuples find 40 SDR failures. No default build jobs are added.
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-sdr-seven-research).

## Grouped modulus-107 certificate exports

[The grouped-export generator](../scripts/prepare_g2_seven107_groups.py) reproduces
eleven conjunction statements covering all 634 terminal-certificate theorems
of the modulus-107 exclusion. Each independent proof carries its own local
witness data. All eleven groups pass both Lean revisions, with complete
component-type checks and standard axioms. The generator reproduces all 22
verified source files byte for byte. The assembly is now checked as described
below; the exact platform dependency layout remains pending.
[Sources, checks and timings](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/g2-seven107-grouped-exports).


## Fast assembly of the grouped modulus-107 proof

[The assembly generator](../scripts/prepare_g2_seven107_assembly.py) composes
all eleven proved conjunctions into the unconditional modulus-107 exclusion.
It exposes 634 component aliases and checks the 28 internal assembly steps
as separate theorems. Supported compilation takes 69.928 seconds
with one Lean thread; a monolithic imported-group probe exceeded 367 seconds
before being stopped. Both revisions pass all 683 type/axiom checks, 664
original helper-type comparisons and seven core definition-value comparisons.
The proof dependency audit confirms all eleven groups are used, without
direct component shortcuts or reuse of the original final exclusion.

The generator reproduces the verified sources from the existing evidence
archives and copies the eleven matching group-target sources. These outputs
are checked in a scratch workspace with the recorded dependency caches.
The exact platform layout and upload remain pending. This is a more efficient
composition of an already proved finite exclusion; general G2 remains open.
[Sources, audits, timings and reproducible inputs](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/g2-seven107-grouped-assembly).

## Generic prefix-certificate platform API

The generic API needed by the G2 finite exclusions is checked in its exact
Prove2Me layout: nineteen definitions, nine new reusable theorem/proof nodes
and six existing theorem interfaces, including the already published sorting
theorem. All 34 modules compile on both revisions; all solution types and
dependencies, 31 definition/constructor types and 21 definition values match.
The supported maximum module time is 13.051 seconds with one Lean thread.

The private payloads and all existing dependency files were checked against
live Prove2Me text. The definition and all nine theorem nodes are now
published privately, with ACCEPTED proofs and exact server dependency checks.
The three proved API roots are included in the consolidated DAG. This package
does not prove general G2 or change the three open leaves.
[Exact sources, payloads, compiler facts and audits](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/g2-prefix-api).

## Seven-dimensional bridge completed; generic proof remains the goal

[The bridge](../MinModulus/G2OddSevenDimensions.lean) proves the sharp odd
bound in dimension seven and reduces local general G2 to n>=8. Both Lean
revisions pass 27 type/axiom checks and six definition-value comparisons.
The default library root and required audits pass with checked cached
dependencies. Prove2Me remains at From7 pending connecting proof acceptance.
Further mathematical effort prioritizes the uniform half-degree growth
inequality, not another finite-dimensional campaign.

## Generic repeated-coin growth target

[The generic proof plan](GenericNProofPlan.md) prioritizes arbitrary n.
[RepeatedCoinGrowth.lean](RepeatedCoinGrowth.lean) identifies D_d exactly
with the doubled-coordinate translates of C_(d-2), separates the squarefree
sums, and discharges the degree-two and degree-three growth increments.
The remaining target is |2·A+C_(d-2)|>=|C_(d-1)| for d>=4 and 2d<=n+1.
Its truth would settle full G2; every odd counterexample must force a
strict failure at one such degree. The inequality remains unproved.
Both revisions verify fifteen declarations, twenty literal type/axiom
checks and seven definition values. G1 and G3 still need general proofs.

## Uniform quadratic-translate rigidity

[The new argument](QuadraticTranslateRigidity.md) proves that a squarefree
hit confines an outside quadratic translate to three coordinates, while
four hits force doubled representations. A complete outside translate
therefore supplies all coin-growth inequalities and the sharp odd bound.
Every hypothetical counterexample must have an escape for every outside
shift. Nine declarations pass both revisions with fifteen type/axiom and
seven definition-value checks. The associated finite matrix experiment
has 770 independently verified witnesses; its general rank claim remains
open. These results preserve the focus on arbitrary n.
