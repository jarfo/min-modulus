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
pair implies N >= 2^n - 1. Universal existence of that pair is false, as
the anchored-moment follow-up below now proves. Existence restricted to
N<2^n-1 remains an unproved sufficient condition; general G2 remains open. Both Lean revisions pass 18 literal
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
{0} and gives N >= 2^n-1. Universal existence is false; existence restricted to N<2^n-1 remains
an unproved sufficient condition (see the anchored-moment follow-up below).
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

## Generic single-repeat collision bound

[SingleRepeatFibres](SingleRepeatFibres.md) proves the arbitrary-n,
arbitrary-degree bound r<=binomial(n-r,d-2), exact total incidences, and
a resulting global repeated-sum lower bound. Fourteen declarations pass
both Lean revisions with twenty type/axiom and nine definition-value
checks. The bound is weaker than the general growth target. The archive
also makes the saved cap-three counterexample and earlier fibre probe
reproducible, separately from the uniform Lean proof.

## Parallel G3 structure and witness compatibility

[G3ParallelReview](G3ParallelReview.md) audits the parallel branch and live
mission comment 96b76a47. The exceptional-modulus source passes both Lean
revisions, and four existing private proofs are read back as accepted and
integrated into the consolidated DAG. Four new generic compatibility lemmas
also pass both revisions, making the anchor and tail subtraction conditions
explicit. A target and the omitted tail determine a light witness uniquely.
The required compatible-pair existence theorem remains open.

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

## Large-dimension consequence of the parallel extraction

[TwoEscapeLargeBound](TwoEscapeLargeBound.md) proves that the unproved
TwoEscapeShift predicate would directly give every even-stratum bound
and the G3 obstruction from dimension 52. The existing unconditional
three-escape lower bound contradicts the proposed two-escape extraction
in a hypothetical critical tuple. With G2, the full global bound follows
for all n>=52 without a G3 premise; full arbitrary-n assembly additionally
needs only the explicitly assumed exceptional exclusions below 52.
Six implications pass the original revision and standard-axiom audit.
No supported port or platform upload is claimed, and no generic gate
is closed. This strengthens the explanation of what TwoEscapeShift
would imply; its extraction remains unproved.

## Simultaneous compatible kernel-witness families

[G3KernelFamilies](G3KernelFamilies.md) constructs a family of more than r
compatible coefficient vectors whenever |H|*r<binomial(|A|,k), supported
inside any prescribed coordinate set A and with distinct targets in the
quotient kernel. Zero is included; the other members and every nonzero
pairwise difference are reversible witnesses. Four theorems pass both
revisions. The missing G3 step is control between different families or
a stronger use of the cyclic kernel; no generic gate is closed.

## Generic limitation of balanced G3 isolation

[G3BalancedCountermodel](G3BalancedCountermodel.md) proves, for every
non-power-of-two n>=3, an invalid tuple at the exact exceptional modulus
with no nonzero balanced unit-coefficient zero relation. Binary powers
have injective fixed-rank subset sums modulo every power-gap modulus;
when its removed power exceeds n, binary splitting gives a different
n-coin multiset with the all-ones target. Six theorems pass both revisions.
Consequently fixed-rank separation, quotient counting, and compatible
families alone cannot prove G3. The next step must use stronger validity
constraints, such as one-sided admissible relations with a coefficient
above one. That file leaves the stronger antichain restriction unresolved; the
bounded-coefficient follow-up below settles its limitation for large n. No generic gate is closed.

## Fixed coefficient cutoffs and antichains cannot close generic G3

[G3BoundedCoefficientCountermodel](G3BoundedCoefficientCountermodel.md)
proves that every fixed coefficient cutoff eventually misses invalid
binary tuples at the actual G3 modulus. For any C, non-power-of-two
n>=2^(C+4) admits an invalid tuple with no nonzero balanced zero relation
having -1<=c_i<C. More precisely, every rival binary multiset has ordinary
value 2^s-1 and is supported below s; n>C*s excludes multiplicities <=C.
Here s=floor(log2 n)+1.

For n>=16 the same invalid tuple satisfies the unit-witness negative-support
antichain and Sperner bounds, at every target. Those restrictions therefore
cannot repair the generic G3 inference by themselves. An admissible-relation
argument must exploit a coefficient range growing with n, or introduce
additional structure not implied by bounded isolation. The older heavy
anchored-witness route already permits coefficients growing with n and
is not ruled out by this result. Ten theorems pass both Lean revisions;
the conjecture and all three generic gates remain open.

## Translate rigidity in every degree

[HigherTranslateRigidity](HigherTranslateRigidity.md) extends the quadratic
argument to every degree d. For t outside C_(d-1), one squarefree hit of
A+t in C_d confines all hits to at most d+1 coordinates. At least d+2 hits
force all hits to be repeated. A full outside translate, when n>=d+2,
gives |C_(r+1)|<=|D_(r+d)| for every r>=0 by an injective translation.
The five uniform theorems pass both revisions, exact types, definitions
and standard axioms. The needed complete translate is not known to exist;
for d>2 the resulting degree jump exceeds one. Thus this does not settle
the remaining generic G2 growth inequality.

## Limits of averaged anchored overlaps

[AnchoredMomentCounterexample](AnchoredMomentCounterexample.md) reuses the
valid tuple (0,11,8,6) modulo 15. Its pair intersections sum to 25>24 and
its triple intersections sum to 9>8. Every distinct pair has more than one
common point, although the union is all 15 residues. Hence averaging does
not repair the quarter/eighth bounds, and universal existence of a
relation-free pair is false. A condition restricted to hypothetical
counterexamples N<2^n-1 remains an unproved possible sufficient condition.
Four further theorems pass both revisions. No generic gate is closed.

## Two quadratic escapes from every outside translate

[QuadraticOneEscape](QuadraticOneEscape.md) connects quadratic rigidity
to the existing unconditional odd one-escape affine-doubling theorem.
For n>=5, n-1 hits give an injective partial matching to doubled
coordinates; reversing it leaves at most one forward escape. Therefore
N<2^n-1 forces two distinct quadratic escapes at every outside shift.
All three transfer lemmas and both applications now pass both revisions.
The full one-escape dependency port keeps 122 named declarations in
26 source modules, with three explicit simp portability edits. Original
types, definitions and standard axioms match while avoiding the
1025-module import closure.
These two applications and ten supporting theorem nodes are now
accepted on Prove2Me. All 633 recorded proof dependency sets match,
and the three generic open leaves are unchanged. The required generic
repeated-sum growth is still open.

## Quadratic escape counts inherit affine restrictions

[QuadraticEscapeCounts](QuadraticEscapeCounts.md) proves that, at odd
modulus, four outside quadratic hits force equality with the forward
affine hit count at offset -t. Always, quadratic escapes are at least
min(n-3, affine escapes). Both count proofs pass both revisions.
The existing exact-stratum affine bound consequently gives
n<(r+1)^2*(floor(log2 n)+1)+3*(r+1) for every outside shift's quadratic
escape count r in an odd counterexample. That quantitative application
passes the original full-source revision and a supported split proof.
All three split proofs have matching original types, definition values
and exact dependency sets; their five external interfaces are Proved.
All three nodes are now accepted on Prove2Me and connected to the
consolidated DAG. All 636 proof dependency sets across 19 bundles match.
G1, G2 and G3 remain open, and independent repeated-sum growth is still needed.

## Squarefree midpoints give many escapes in every even repeated degree

[Squarefree midpoint escapes](SquarefreeMidpointEscapes.md) proves that
the midpoint of a squarefree 2k-sum lies outside C_k and has at most
2k+1 coordinate hits in C_(k+1), for every k>=1. At odd order, each
support therefore yields at least n-(2k+1) distinct repeated sums of
degree 2k+2 outside 2·C_(k+1). In particular, every coordinate pair
has at least n-3 quartic escapes, with no counterexample premise.
The proof combines the earlier translate rigidity with validity of a
squarefree sum on 2k+2 coordinates. All five theorem statements pass
both revisions and standard-axiom audits. All five midpoint nodes are now accepted on Prove2Me. Overlap across different supports remains uncontrolled;
the full repeated-sum growth inequality and G1/G2/G3 remain open.

The squarefree midpoint results now have a verified five-node split
export. Both revisions pass all five original-type and exact dependency
checks, and five definition values match. Only two existing Proved
interfaces are reused; no definitions are added. Metadata and live
preflight pass. Publication is complete; the three generic gates remain open.
The consolidated DAG has 916 nodes and 2116 edges. All 641 proof dependency sets across 20 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

## Midpoint rigidity controls hits outside the squarefree support

[Midpoint support rigidity](MidpointSupportRigidity.md) proves that two
hits outside a squarefree support S force all hits to be those two.
Thus at most two hits lie outside S. For |S|=2k,k>=1, odd modulus
then gives at least n-(2k+2) single-repeat values anchored outside S
and escaping 2·C_(k+1). This improves the previous bound after excluding
anchors in S, and applies at every even repeated degree. All four
proofs pass both revisions, eight type comparisons, four definition
values and standard axioms. All four support-rigidity nodes are accepted on Prove2Me. Controlling
overlap across supports is still necessary; G1, G2 and G3 remain open.

The midpoint support results now have a verified four-node split export.
Both revisions pass four original-type and exact dependency checks,
and four definition values match. Four Proved interfaces are reused,
with no new definitions. Metadata and live preflight pass. Publication is complete; overlap across supports and the three
generic gates remain open.
The consolidated DAG has 924 nodes and 2135 edges. All 645 proof dependency sets across 21 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

## Outside coefficient probes have trivial joint kernel

[Single-repeat probes](SingleRepeatProbes.md) defines the individual
operators underlying the proposed repeated-sum rank matrices. Validity
makes a fixed anchor/removal probe isolate one squarefree coefficient.
For every k>=1,n>=2k+2 at odd modulus, the midpoint escape theorem
therefore makes all probes outside 2·C_(k+1) jointly determine every
coefficient of support size 2k+1. Both proofs pass both revisions,
five printed-type checks, three definition values and standard axioms.
Finding one full-rank combination of the probes remains open; the
joint-kernel statement alone does not establish the required global
count. Both probe theorem nodes are now Proved on Prove2Me; G1/G2/G3 remain open.

The coefficient-probe results now have a verified two-node split export.
Both revisions pass two original-type and exact dependency checks,
and three definition values match. Two Proved interfaces are reused,
with one new lightweight definition bundle. Metadata and live preflight
pass. Publication is complete; the single full-rank combination and
G1/G2/G3 remain open.
The consolidated DAG has 929 nodes and 2145 edges. All 647 proof dependency sets across 22 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

## Residual trades and rooted balances constrain repeated-sum fibres

[Residual-trade rigidity](ResidualTradeRigidity.md) proves that, in every
positive residual degree, the aggregate residual multiset determines the
selected anchor subset. In quartic fibres, two rooted residual balances
cannot have disjoint anchor supports. Both theorems hold for arbitrary n
in any abelian group with injective doubling. Both revisions pass three
printed-type checks, one definition value and standard-axiom audits.
The proposed graph consequence is at most one odd residual cycle and a
half-dimension fibre cap; that graph argument is not yet formalized.
Both residual-trade nodes are now Proved on Prove2Me. Global repeated-sum growth, the
full-rank coefficient combination and G1/G2/G3 remain open.

The residual-trade results now have a verified two-node split export.
Both revisions pass two original-type and exact dependency checks,
and the ValidTuple definition matches. One Proved interface is reused,
with no new definitions. Metadata and live preflight pass. Publication is complete; the graph counting consequence and
G1/G2/G3 remain open.
The consolidated DAG has 933 nodes and 2153 edges. All 649 proof dependency sets across 23 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

## Even and odd residual cycles translate to multiset balances

[Residual cycle balances](ResidualCycleBalances.md) excludes every nonempty
alternating even residual cycle, encoded by finite maps and a reconnection
permutation, inside a quartic fibre. A second combinatorial theorem turns
an odd endpoint cycle into a rooted residual balance with two copies of
its initial vertex. Both results are uniform in the dimension and cycle
length. Both revisions pass three printed types, the ValidTuple definition
value and standard-axiom checks. Both residual-cycle nodes are now Proved on Prove2Me.
The actual graph-walk interface, graph decomposition and half-dimension
fibre cap remain open, as do global repeated-sum growth and G1/G2/G3.

The residual-cycle results now have a verified two-node split export.
Both revisions pass two original-type and exact dependency checks,
and the ValidTuple definition matches. One Proved interface is reused,
with no new definitions. Metadata and live preflight pass. Publication is complete; the graph counting consequence and
G1/G2/G3 remain open.
The consolidated DAG has 936 nodes and 2158 edges. All 651 proof dependency sets across 24 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

## A residual graph with unique anchors outside its vertices

[Quartic residual graph](QuarticResidualGraph.md) defines graph edges
from the two-element residual supports of an anchor family. Three
interfaces prove that single-repeat residual supports avoid every
anchor, equal residual supports determine equal anchors under injective
doubling, and graph endpoints lie outside the anchor set. The definition
and all interfaces pass both revisions, five printed types, two definition
values and standard axioms. All five graph/helper nodes are now Proved on Prove2Me.
Instantiation for actual fibres, the graph-walk cycle interface and the
graph counting consequence remain open, as do generic G1/G2/G3.

The graph interfaces now have a verified five-node split export, including
two existing helpers being made reusable on Prove2Me. Both revisions pass
five original-type and exact dependency checks and two definition values.
One Proved external interface is reused, with one graph definition bundle.
The injectivity helper uses a shorter singleton proof of the same type;
the other four bodies match the checked source. Metadata and live preflight
pass. Publication is complete; actual-fibre and graph-walk instantiation,
graph counting and G1/G2/G3 remain open.
The consolidated DAG has 947 nodes and 2179 edges. All 656 proof dependency sets across 25 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

## Actual fibre supports and exact residual graph edge counts

[Actual-fibre graph realization](SingleRepeatGraphRealization.md) chooses
residual supports simultaneously for every anchor in an actual single-repeat
fibre, in every degree and abelian group. A second theorem counts exactly
one residual graph edge per anchor for two-element supports in a valid
fibre with injective doubling. Both revisions pass five printed types,
three definition values and standard axioms. Both actual-fibre and edge-count results are
now Proved on Prove2Me. They provide the actual-fibre realization
and edge-count interfaces; graph-walk translation and graph decomposition
remain, along with the global growth/rank argument and G1/G2/G3.

The actual-fibre and edge-count results have a verified two-node split
export. Both revisions pass the two exact original-type and dependency
checks and three definition-value checks. The source proof bodies are
retained. One fibre definition bundle is new, and one Proved external
interface is reused. Metadata and exact server proof readbacks pass. Publication is
complete; graph-walk instantiation, decomposition and G1/G2/G3 remain open.
The consolidated DAG has 951 nodes and 2185 edges. All 658 proof dependency sets across 26 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

## Odd cycles in the residual graph

[Residual graph cycles](ResidualGraphCycles.md) now gives injective anchor
labels for every graph trail and proves that every cycle of a valid
quartic residual graph has odd length when doubling is injective. This
connects the finite even-cycle identity to actual SimpleGraph walks.
Both revisions pass five exact printed types, three definition values
and standard axioms, with identical source bodies. The odd-trail rooted balance and common-edge graph interfaces are
also proved in ResidualGraphOddBalances.lean.
Graph decomposition, the prospective fibre cap, global growth/rank and
G1/G2/G3 remain open. Both cycle results are now Proved on Prove2Me.

## Rooted graph balances and shared cycle edges

[Odd graph balances](ResidualGraphOddBalances.md) proves that every odd
closed trail supplies a rooted residual balance on disjoint anchor sets,
with each support an edge of that trail. In a valid single-repeat quartic
family with injective doubling, any two actual graph cycles share an edge.
Both revisions pass five exact printed types, three definition values
and standard axioms with identical source bodies. Both odd-balance results are
now Proved on Prove2Me. Graph decomposition and counting, the
proposed half-dimension fibre cap, global growth/rank and G1/G2/G3 remain open.

The four concrete graph-cycle results have one verified split export.
Both revisions pass four exact original types and dependency sets and
two definition-value checks. Four external Proved theorem interfaces
are reused, with no new definitions. All four original bodies are retained.
The shared-edge theorem is the terminal root. Metadata and live preflight
pass; publication is complete. The consolidated DAG has 958 nodes and 2203 edges. All 662 proof dependency sets across 27 bundles match. G1/P6, G2/From7 and G3/From7 remain open. Graph decomposition, the prospective fibre
cap, global growth/rank and G1/G2/G3 remain open.

## Even-degree edge subsets and graph parity

Three general finite-graph lemmas are proved: nonempty even-degree
graphs contain cycles; under pairwise cycle-edge intersection, every
nonempty even-degree subgraph is one cycle; if those cycles are odd,
an even-degree subgraph with even edge count is empty. The parity
code and induced residual-graph application are also complete.
All six graph parity/counting/fibre statements are private and Proved,
with verified submissions and exact server proof-source readbacks.
The actual-fibre theorem is the terminal supporting root. It retains
all six statements and reuses five existing Proved interfaces. Both
revisions pass six exact original types and dependency sets, three
definition-value checks and all six original proof bodies.

The consolidated DAG has 977 nodes and 2249 edges. All 668 proof dependency sets across 28 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

## A vertex-parity code bounds the number of graph edges

A finite graph whose cycles are odd and pairwise share an edge has
at most as many edges as vertices. An injective vertex-parity code
proves this uniformly, without enumeration. Its residual-graph
application now proves the half-dimension quartic fibre bound.
All six graph parity/counting/fibre statements are private and Proved,
with verified submissions and exact server proof-source readbacks.
The actual-fibre theorem is the terminal supporting root. It retains
all six statements and reuses five existing Proved interfaces. Both
revisions pass six exact original types and dependency sets, three
definition-value checks and all six original proof bodies.

The consolidated DAG has 977 nodes and 2249 edges. All 668 proof dependency sets across 28 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

## Quartic single-repeat fibres occupy at most half the coordinates

For every valid tuple in a group with injective doubling, a quartic
single-repeat fibre has at most floor(n/2) anchors. This applies to
all odd cyclic groups. The family graph has |R| edges on at most
n-|R| complementary vertices. The graph edge bound gives 2|R|<=n.
Global repeated-sum growth and the full-rank combination remain open.
All six graph parity/counting/fibre statements are private and Proved,
with verified submissions and exact server proof-source readbacks.
The actual-fibre theorem is the terminal supporting root. It retains
all six statements and reuses five existing Proved interfaces. Both
revisions pass six exact original types and dependency sets, three
definition-value checks and all six original proof bodies.

The consolidated DAG has 977 nodes and 2249 edges. All 668 proof dependency sets across 28 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

## Six-node export for the generic quartic fibre bound

All six graph parity/counting/fibre statements are private and Proved,
with verified submissions and exact server proof-source readbacks.
The actual-fibre theorem is the terminal supporting root. It retains
all six statements and reuses five existing Proved interfaces. Both
revisions pass six exact original types and dependency sets, three
definition-value checks and all six original proof bodies.

The consolidated DAG has 977 nodes and 2249 edges. All 668 proof dependency sets across 28 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

## Absolute repeated-sum bounds at the two central degrees

For k=floor(n/2) and k=ceil(n/2), the absolute target
|D_k|+1 >= sum_{j<k} choose(n,j) suffices for G2. The bound is
proved through degree three, so every odd counterexample violates
it at a central degree k>=4. No successive-growth hypothesis is
required. The uniform central bounds remain the open step.

All four central-degree reductions are private and Proved, with verified
submissions and exact server proof-source readbacks. Both revisions pass
four original types and dependency sets, four definition comparisons,
fourteen original inline helper types and the inline subsetCoinSums value.
All original proof and helper bodies are retained. Four existing Proved
interfaces are reused. The conditional G2 theorem is the supporting root.

The consolidated DAG has 977 nodes and 2249 edges. All 672 proof dependency sets across 29 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The central absolute bounds from degree four onward remain unproved.
These are conditional reductions and do not close generic G2.

## Four-node export for the central-degree G2 reduction

For k=floor(n/2) and k=ceil(n/2), the absolute target
|D_k|+1 >= sum_{j<k} choose(n,j) suffices for G2. The bound is
proved through degree three, so every odd counterexample violates
it at a central degree k>=4. No successive-growth hypothesis is
required. The uniform central bounds remain the open step.

All four central-degree reductions are private and Proved, with verified
submissions and exact server proof-source readbacks. Both revisions pass
four original types and dependency sets, four definition comparisons,
fourteen original inline helper types and the inline subsetCoinSums value.
All original proof and helper bodies are retained. Four existing Proved
interfaces are reused. The conditional G2 theorem is the supporting root.

The consolidated DAG has 977 nodes and 2249 edges. All 672 proof dependency sets across 29 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The central absolute bounds from degree four onward remain unproved.
These are conditional reductions and do not close generic G2.

## A concrete matrix criterion for repeated-sum cardinality

A single coefficient-recovering probe matrix outside 2*C_(k+1) forces
|D_(2k+2)| >= |C_(k+1)|+choose(n,2k+1). Its quartic specialization for
valid tuples gives choose(n+1,2)+choose(n,3). The recovering matrix is
still unproved; joint recovery by all separate probes does not suffice.
The higher-degree bound also lacks some terms of the central target.

All four weighted-probe implications are private and Proved, with
verified submissions and exact server proof-source readbacks. The new
weighted-probe definition is private and verified. Both revisions pass
four exact original types and dependency sets, five definition values
and two original inline helper types. All original proof and helper
bodies are retained. Two existing Proved interfaces are reused. The
conditional quartic result is the terminal supporting root.

The consolidated DAG has 984 nodes and 2263 edges. All 676 proof dependency sets across 30 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The coefficient-recovering matrix remains unproved. In higher degrees,
more lower-binomial terms are needed. These implications do not close G2.

## Four-node export for the weighted-probe cardinality criterion

A single coefficient-recovering probe matrix outside 2*C_(k+1) forces
|D_(2k+2)| >= |C_(k+1)|+choose(n,2k+1). Its quartic specialization for
valid tuples gives choose(n+1,2)+choose(n,3). The recovering matrix is
still unproved; joint recovery by all separate probes does not suffice.
The higher-degree bound also lacks some terms of the central target.

All four weighted-probe implications are private and Proved, with
verified submissions and exact server proof-source readbacks. The new
weighted-probe definition is private and verified. Both revisions pass
four exact original types and dependency sets, five definition values
and two original inline helper types. All original proof and helper
bodies are retained. Two existing Proved interfaces are reused. The
conditional quartic result is the terminal supporting root.

The consolidated DAG has 984 nodes and 2263 edges. All 676 proof dependency sets across 30 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The coefficient-recovering matrix remains unproved. In higher degrees,
more lower-binomial terms are needed. These implications do not close G2.

## Weighted-probe rank permits symbolic coefficient fields

The fixed-matrix coefficient-recovery hypothesis gives
|D_(2k+2)| >= |C_(k+1)| + choose(n,2k+1) over any coefficient field,
including an infinite field with symbolic matrix entries. The proof uses
an injective linear map and finite-dimensional rank. For valid tuples,
the quartic consequence is |D4| >= choose(n+1,2)+choose(n,3).
The existence of a recovering matrix remains open. Higher degrees
still require missing lower-binomial terms for the central target.

All four field-linear probe results are private and Proved, with verified
submissions and exact server proof-source readbacks. Both revisions pass
four original types and dependency sets, five definition comparisons
and two original inline helper types. All original theorem and helper
bodies are retained. Four Proved interfaces are reused, with no new
definition. The conditional quartic bound over any field is the root.

The consolidated DAG has 990 nodes and 2278 edges. All 680 proof dependency sets across 31 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The recovering matrix and missing higher-degree binomial terms remain unproved.
These are conditional rank implications and do not close generic G2.

## Four-node export for symbolic-field weighted-probe rank

The fixed-matrix coefficient-recovery hypothesis gives
|D_(2k+2)| >= |C_(k+1)| + choose(n,2k+1) over any coefficient field,
including an infinite field with symbolic matrix entries. The proof uses
an injective linear map and finite-dimensional rank. For valid tuples,
the quartic consequence is |D4| >= choose(n+1,2)+choose(n,3).
The existence of a recovering matrix remains open. Higher degrees
still require missing lower-binomial terms for the central target.

All four field-linear probe results are private and Proved, with verified
submissions and exact server proof-source readbacks. Both revisions pass
four original types and dependency sets, five definition comparisons
and two original inline helper types. All original theorem and helper
bodies are retained. Four Proved interfaces are reused, with no new
definition. The conditional quartic bound over any field is the root.

The consolidated DAG has 990 nodes and 2278 edges. All 680 proof dependency sets across 31 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The recovering matrix and missing higher-degree binomial terms remain unproved.
These are conditional rank implications and do not close generic G2.

## Valid odd cyclic tuples extend to every larger dimension

Every valid odd cyclic tuple embeds into valid odd cyclic tuples in
every larger dimension through an index embedding and an injective
additive map. A new cyclic factor forces the adjoined coordinate's
multiplicity to be one; the Chinese remainder equivalence restores a
cyclic ambient group. Every original additive relation is preserved.
The new modulus may be large, so no min-modulus counterexample follows.

All eight extension/control/diagonal results are private and Proved,
with verified submissions and exact server proof-source readbacks.
Both Mathlib revisions pass eight original types and dependency sets,
five definition values and the original bounded control helper type.
All original theorem and helper bodies are retained. The new control
definition is published; existing probe definitions are reused.
Two supporting roots retain the whole chain. No new finite search is used.

The consolidated DAG has 1003 nodes and 2301 edges. All 688 exact proof dependency sets across 32 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Full-matrix coefficient recovery and the central repeated-sum inequalities
remain open. The extension does not preserve a small modulus; the
diagonal obstruction gives no min-modulus counterexample.

## Diagonal probes fail in every dimension at least four

Valid odd cyclic tuples in every dimension 4+r can contain a cubic
coefficient invisible to every diagonal weighted probe outside 2 C_2.
The fixed control supplies three doubled-pair identities, preserved by
additive transport and the generic odd cyclic extension. Over every
nontrivial coefficient semiring, a nonzero kernel vector refutes exactly
the coefficient-recovery hypothesis of the quartic counting theorem.
Off-diagonal entries remain available in the full-matrix rank problem.

All eight extension/control/diagonal results are private and Proved,
with verified submissions and exact server proof-source readbacks.
Both Mathlib revisions pass eight original types and dependency sets,
five definition values and the original bounded control helper type.
All original theorem and helper bodies are retained. The new control
definition is published; existing probe definitions are reused.
Two supporting roots retain the whole chain. No new finite search is used.

The consolidated DAG has 1003 nodes and 2301 edges. All 688 exact proof dependency sets across 32 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Full-matrix coefficient recovery and the central repeated-sum inequalities
remain open. The extension does not preserve a small modulus; the
diagonal obstruction gives no min-modulus counterexample.

## Verified eight-node diagonal-obstruction export

Valid odd cyclic tuples in every dimension 4+r can contain a cubic
coefficient invisible to every diagonal weighted probe outside 2 C_2.
The fixed control supplies three doubled-pair identities, preserved by
additive transport and the generic odd cyclic extension. Over every
nontrivial coefficient semiring, a nonzero kernel vector refutes exactly
the coefficient-recovery hypothesis of the quartic counting theorem.
Off-diagonal entries remain available in the full-matrix rank problem.

All eight extension/control/diagonal results are private and Proved,
with verified submissions and exact server proof-source readbacks.
Both Mathlib revisions pass eight original types and dependency sets,
five definition values and the original bounded control helper type.
All original theorem and helper bodies are retained. The new control
definition is published; existing probe definitions are reused.
Two supporting roots retain the whole chain. No new finite search is used.

The consolidated DAG has 1003 nodes and 2301 edges. All 688 exact proof dependency sets across 32 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Full-matrix coefficient recovery and the central repeated-sum inequalities
remain open. The extension does not preserve a small modulus; the
diagonal obstruction gives no min-modulus counterexample.

## Weighted probes factor through matrix contractions

Every positive-degree weighted probe is exactly a matrix contraction
followed by grouping entries with equal residue sums. If the matrix
acts injectively on coordinate vectors, the contraction stage preserves
every squarefree coefficient. The statements hold in all dimensions
and degrees over arbitrary semirings, without validity or oddness.
The contraction recovery theorem does not involve the tuple or group.

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

## Four-node export for weighted-probe contractions

Every positive-degree weighted probe is exactly a matrix contraction
followed by grouping entries with equal residue sums. If the matrix
acts injectively on coordinate vectors, the contraction stage preserves
every squarefree coefficient. The statements hold in all dimensions
and degrees over arbitrary semirings, without validity or oddness.
The contraction recovery theorem does not involve the tuple or group.

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

## Translated squarefree sum packing

For a valid tuple in any additive commutative group, let S_k be its
k-element subset-sum values. If t is absent from S_k-S_k, then
|(S_(k+1)+t) intersect S_(k+1)| <= binomial(2k+2,k+1).
In particular, squarefree pair-sum translates meet in at most six points
when their shift is not a coordinate difference. This holds for every n,
without cyclicity or oddness. The proof cancels shared coordinates and
packs separating-permutation events using the existing uncrossing lemma.

All five translated squarefree packing results are private and Proved.
Verified submissions and exact server proof-source readbacks pass.
Both revisions verify five original target types and dependency sets,
nine original helper types, and the validity and separating-permutation
definition values. Every original proof body is retained. One existing
proved interface is reused; no new definition bundle is required.
A single supporting root retains all five results.

The consolidated DAG has 1019 nodes and 2330 edges. All 697 exact proof dependency sets across 34 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The quartic application still needs control of anchor pairs whose doubled
difference is a coordinate difference. The absolute quartic and central
bounds and all generic gates remain open.

## Five-node export for translated squarefree packing

For a valid tuple in any additive commutative group, let S_k be its
k-element subset-sum values. If t is absent from S_k-S_k, then
|(S_(k+1)+t) intersect S_(k+1)| <= binomial(2k+2,k+1).
In particular, squarefree pair-sum translates meet in at most six points
when their shift is not a coordinate difference. This holds for every n,
without cyclicity or oddness. The proof cancels shared coordinates and
packs separating-permutation events using the existing uncrossing lemma.

All five translated squarefree packing results are private and Proved.
Verified submissions and exact server proof-source readbacks pass.
Both revisions verify five original target types and dependency sets,
nine original helper types, and the validity and separating-permutation
definition values. Every original proof body is retained. One existing
proved interface is reused; no new definition bundle is required.
A single supporting root retains all five results.

The consolidated DAG has 1019 nodes and 2330 edges. All 697 exact proof dependency sets across 34 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The quartic application still needs control of anchor pairs whose doubled
difference is a coordinate difference. The absolute quartic and central
bounds and all generic gates remain open.

## Coordinate-difference pair-sum packing

For a valid tuple in an additive commutative group with injective
doubling, fix distinct p,q and an allowed coordinate set A. The squarefree
pair-sum values on A have at most |A|-1 matches under g_p-g_q if both
endpoints belong to A, and no matches if either endpoint is absent.
Overlapping matches are exactly {q,c},{p,c}; at most one additional
disjoint match exists. This gives the n-1 bound on the full tuple and
endpoint exclusion on every restricted tuple, uniformly in n.

All six coordinate-difference packing results are private and Proved.
Verified submissions and exact server proof-source readbacks pass.
Both revisions verify six original target types and dependency sets,
two reused helper types, and the ValidTuple definition value. Every
original proof body is retained. Three existing proved interfaces are
reused; no new definition bundle is required. One supporting root
retains all six results.

The consolidated DAG has 1031 nodes and 2360 edges. All 703 exact proof dependency sets across 35 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The restricted pair-intersection bounds are now available. Combining them
into a global quartic estimate and proving all central degrees remain
open, as do generic G1/G2/G3.

A next target in every degree is the exact recurrence
I_(k+1)(A,g_p-g_q)=binomial(|A|-2,k)+I_k(A without {p,q},2(g_p-g_q)),
where I_d is the intersection size of squarefree d-sum values and their
translate, and p,q belong to A. This would lower the degree by one while
removing two coordinates, preserving the central-degree relation. The
cardinality recurrence is now proved in CoordinateDifferenceRecursion.lean;
see the exact recurrence milestone below.

## Six-node export for coordinate-difference packing

For a valid tuple in an additive commutative group with injective
doubling, fix distinct p,q and an allowed coordinate set A. The squarefree
pair-sum values on A have at most |A|-1 matches under g_p-g_q if both
endpoints belong to A, and no matches if either endpoint is absent.
Overlapping matches are exactly {q,c},{p,c}; at most one additional
disjoint match exists. This gives the n-1 bound on the full tuple and
endpoint exclusion on every restricted tuple, uniformly in n.

All six coordinate-difference packing results are private and Proved.
Verified submissions and exact server proof-source readbacks pass.
Both revisions verify six original target types and dependency sets,
two reused helper types, and the ValidTuple definition value. Every
original proof body is retained. Three existing proved interfaces are
reused; no new definition bundle is required. One supporting root
retains all six results.

The consolidated DAG has 1031 nodes and 2360 edges. All 703 exact proof dependency sets across 35 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The restricted pair-intersection bounds are now available. Combining them
into a global quartic estimate and proving all central degrees remain
open, as do generic G1/G2/G3.

A next target in every degree is the exact recurrence
I_(k+1)(A,g_p-g_q)=binomial(|A|-2,k)+I_k(A without {p,q},2(g_p-g_q)),
where I_d is the intersection size of squarefree d-sum values and their
translate, and p,q belong to A. This would lower the degree by one while
removing two coordinates, preserving the central-degree relation. The
cardinality recurrence is now proved in CoordinateDifferenceRecursion.lean;
see the exact recurrence milestone below.

## Exact all-degree coordinate-difference recurrence

For every valid tuple in an additive commutative group and distinct p,q
in an allowed coordinate set A, the exact squarefree intersection formula is
I_(k+1)(A,g_p-g_q)=binomial(|A|-2,k)+I_k(A without {p,q},2(g_p-g_q)).
If either endpoint is missing, the intersection is empty in every degree.
No injectivity of doubling or odd-order hypothesis is needed. The proof
uses explicit normal/repeated support bijections and the exact projection
from support matches to common values.

All ten all-degree recurrence results are private and Proved. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify ten original target types and dependency sets, two reused
interface types and two definition values. Every original proof body is
retained. Two existing proved interfaces and one lightweight definition
bundle are used. Two supporting roots retain the complete recurrence and
all-degree endpoint exclusion.

The consolidated DAG has 1051 nodes and 2405 edges. All 713 exact proof dependency sets across 36 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The exact recurrence is proved. Its residual doubled shift need not be a
coordinate difference on the remaining coordinates. Controlling this
remainder and proving the absolute central bounds remain open, as do
generic G1/G2/G3.

## Verified ten-theorem recurrence export

For every valid tuple in an additive commutative group and distinct p,q
in an allowed coordinate set A, the exact squarefree intersection formula is
I_(k+1)(A,g_p-g_q)=binomial(|A|-2,k)+I_k(A without {p,q},2(g_p-g_q)).
If either endpoint is missing, the intersection is empty in every degree.
No injectivity of doubling or odd-order hypothesis is needed. The proof
uses explicit normal/repeated support bijections and the exact projection
from support matches to common values.

All ten all-degree recurrence results are private and Proved. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify ten original target types and dependency sets, two reused
interface types and two definition values. Every original proof body is
retained. Two existing proved interfaces and one lightweight definition
bundle are used. Two supporting roots retain the complete recurrence and
all-degree endpoint exclusion.

The consolidated DAG has 1051 nodes and 2405 edges. All 713 exact proof dependency sets across 36 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The exact recurrence is proved. Its residual doubled shift need not be a
coordinate difference on the remaining coordinates. Controlling this
remainder and proving the absolute central bounds remain open, as do
generic G1/G2/G3.

## All-degree fibre transport of doubled differences

In a single-repeat fibre with anchor set R and arbitrary residual degree,
a coordinate representation of a doubled difference between fibre anchors
has both endpoints outside all of R. Under injective doubling, any family
E of represented ordered anchor pairs satisfies
|E|<=(n-|R|)*(n-|R|-1), by injection into complement pairs. If all distinct
anchor pairs are represented and |R|>=2, then |R|<=n-|R|. The representation
hypothesis is explicit and is not claimed for arbitrary fibres.

All four all-degree fibre transport results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, four
external interface types, two original inline helper types and two
definition values. Every original proof body is retained. Four existing
proved interfaces are reused; no new definition bundle is introduced.
One supporting root retains the entire four-theorem chain.

The consolidated DAG has 1059 nodes and 2424 edges. All 717 exact proof dependency sets across 37 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The fibre bounds are proved. Turning these collision restrictions into
enough distinct repeated values, the absolute central inequalities and
generic G1/G2/G3 remain open.

## Verified four-theorem fibre transport export

In a single-repeat fibre with anchor set R and arbitrary residual degree,
a coordinate representation of a doubled difference between fibre anchors
has both endpoints outside all of R. Under injective doubling, any family
E of represented ordered anchor pairs satisfies
|E|<=(n-|R|)*(n-|R|-1), by injection into complement pairs. If all distinct
anchor pairs are represented and |R|>=2, then |R|<=n-|R|. The representation
hypothesis is explicit and is not claimed for arbitrary fibres.

All four all-degree fibre transport results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, four
external interface types, two original inline helper types and two
definition values. Every original proof body is retained. Four existing
proved interfaces are reused; no new definition bundle is introduced.
One supporting root retains the entire four-theorem chain.

The consolidated DAG has 1059 nodes and 2424 edges. All 717 exact proof dependency sets across 37 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The fibre bounds are proved. Turning these collision restrictions into
enough distinct repeated values, the absolute central inequalities and
generic G1/G2/G3 remain open.

## Global single-repeat incidence and collision bounds

For arbitrary selected values Y, single-repeat incidences equal a sum
over residual supports and outside anchors. At odd modulus, the midpoint
escape bound gives (n-(2k+2))*choose(n,2k) incidences outside 2*C_(k+1).
The resulting value bound loses exactly a sum of pair collisions; this
sum is reindexed by unordered anchor pairs. Common values of anchors a,b
inject into translated squarefree intersections on coordinates excluding
a,b, with shift 2*(g_a-g_b). These identities apply in arbitrary degree.

All six global incidence results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify six original target types and dependency sets, three
external interface types, three inline helper types, one bundled helper
type, four ordinary definition values and the inline configuration
definition value. Every original proof body is retained. Three existing
proved interfaces are reused; no new definition bundle is introduced.
Three supporting roots retain all six results.

The consolidated DAG has 1069 nodes and 2444 edges. All 723 exact proof dependency sets across 38 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The incidence identities and collision reductions are proved. Bounding
the total loss sufficiently for the absolute central inequalities and
generic G1/G2/G3 remains open.

## Verified six-theorem incidence export

For arbitrary selected values Y, single-repeat incidences equal a sum
over residual supports and outside anchors. At odd modulus, the midpoint
escape bound gives (n-(2k+2))*choose(n,2k) incidences outside 2*C_(k+1).
The resulting value bound loses exactly a sum of pair collisions; this
sum is reindexed by unordered anchor pairs. Common values of anchors a,b
inject into translated squarefree intersections on coordinates excluding
a,b, with shift 2*(g_a-g_b). These identities apply in arbitrary degree.

All six global incidence results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify six original target types and dependency sets, three
external interface types, three inline helper types, one bundled helper
type, four ordinary definition values and the inline configuration
definition value. Every original proof body is retained. Three existing
proved interfaces are reused; no new definition bundle is introduced.
Three supporting roots retain all six results.

The consolidated DAG has 1069 nodes and 2444 edges. All 723 exact proof dependency sets across 38 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The incidence identities and collision reductions are proved. Bounding
the total loss sufficiently for the absolute central inequalities and
generic G1/G2/G3 remains open.

## Quartic collision bounds and sparse differences

For a valid tuple with injective doubling, ordinary anchor pairs have
at most six common quartic values. Pairs whose doubled difference is
represented by two distinct outside coordinates have at most n-3. If C
counts those exceptional unordered pairs and n>=9, the global pair loss
is at most 6*choose(n,2)+(n-9)*C. At odd modulus and n>=14, the explicit
hypothesis 3*(n-9)*C<=2*(n-14)*choose(n,2) yields the absolute quartic
bound |D4|>=choose(n+1,2)+choose(n,3). Sparsity is not asserted for
arbitrary valid tuples.

All six quartic collision results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify six original target types and dependency sets, eight
external interface types, two original inline helper types and five
definition values. Every original proof body is retained. One new
definition records exceptional unordered anchor pairs. One supporting
root retains the complete six-theorem chain.

The consolidated DAG has 1082 nodes and 2478 edges. All 729 exact proof dependency sets across 39 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The conditional quartic bound is proved. Dense exceptional cases, the
higher absolute central inequalities and generic G1/G2/G3 remain open.

## Verified six-theorem quartic collision export

For a valid tuple with injective doubling, ordinary anchor pairs have
at most six common quartic values. Pairs whose doubled difference is
represented by two distinct outside coordinates have at most n-3. If C
counts those exceptional unordered pairs and n>=9, the global pair loss
is at most 6*choose(n,2)+(n-9)*C. At odd modulus and n>=14, the explicit
hypothesis 3*(n-9)*C<=2*(n-14)*choose(n,2) yields the absolute quartic
bound |D4|>=choose(n+1,2)+choose(n,3). Sparsity is not asserted for
arbitrary valid tuples.

All six quartic collision results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify six original target types and dependency sets, eight
external interface types, two original inline helper types and five
definition values. Every original proof body is retained. One new
definition records exceptional unordered anchor pairs. One supporting
root retains the complete six-theorem chain.

The consolidated DAG has 1082 nodes and 2478 edges. All 729 exact proof dependency sets across 39 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The conditional quartic bound is proved. Dense exceptional cases, the
higher absolute central inequalities and generic G1/G2/G3 remain open.

## Quadratic incidence counts and improved quartic sparsity

In every degree, twice the single-repeat incidence count is at most
three times the occupied repeated-value count plus the pair-collision
count. The scalar inequality is exact at fibre sizes two and three.
Together with the escape supply and the quartic collision cap, this
proves |D4|>=choose(n+1,2)+choose(n,3) at odd modulus for n>=12 under
the explicit condition (n-9)*C<=(n-12)*choose(n,2). The condition is
weaker than the preceding quartic criterion, but is not asserted for
arbitrary valid tuples.

All four quadratic counting results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, five
external interface types, three original inline helper types and five
definition values. Every original proof body is retained. Existing
definitions are reused; no new definition bundle is introduced. One
supporting root retains the complete four-theorem chain.

The consolidated DAG has 1089 nodes and 2496 edges. All 733 exact proof dependency sets across 40 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The conditional quartic bound is proved. Dense exceptional cases, the
higher absolute central inequalities and generic G1/G2/G3 remain open.

## Verified four-theorem quadratic counting export

In every degree, twice the single-repeat incidence count is at most
three times the occupied repeated-value count plus the pair-collision
count. The scalar inequality is exact at fibre sizes two and three.
Together with the escape supply and the quartic collision cap, this
proves |D4|>=choose(n+1,2)+choose(n,3) at odd modulus for n>=12 under
the explicit condition (n-9)*C<=(n-12)*choose(n,2). The condition is
weaker than the preceding quartic criterion, but is not asserted for
arbitrary valid tuples.

All four quadratic counting results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, five
external interface types, three original inline helper types and five
definition values. Every original proof body is retained. Existing
definitions are reused; no new definition bundle is introduced. One
supporting root retains the complete four-theorem chain.

The consolidated DAG has 1089 nodes and 2496 edges. All 733 exact proof dependency sets across 40 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The conditional quartic bound is proved. Dense exceptional cases, the
higher absolute central inequalities and generic G1/G2/G3 remain open.

## Negative affine doubling domains

For a valid tuple with injective doubling, a partial map satisfying
g(f(i))+2*g(i)=t on S can take i back into S only when f(i)=i. This
negative affine map is injective on S, so its nonfixed images inject
into the complement of S. Hence 2*|S|<=n+|fixed points in S|, with the
fixed-point term explicit. These statements do not extract an affine
block from a dense represented-difference graph.

All three negative affine domain results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify three original target types and dependency sets, two
external interface types, one original inline helper type and the
ValidTuple definition value. Every original proof body is retained.
No new definition bundle is introduced. One supporting root retains
the complete three-theorem chain.

The consolidated DAG has 1095 nodes and 2510 edges. All 736 exact proof dependency sets across 41 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The domain restrictions are proved. Affine structure
extraction, absolute central inequalities and generic G1/G2/G3 remain open.

## Verified three-theorem negative affine export

For a valid tuple with injective doubling, a partial map satisfying
g(f(i))+2*g(i)=t on S can take i back into S only when f(i)=i. This
negative affine map is injective on S, so its nonfixed images inject
into the complement of S. Hence 2*|S|<=n+|fixed points in S|, with the
fixed-point term explicit. These statements do not extract an affine
block from a dense represented-difference graph.

All three negative affine domain results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify three original target types and dependency sets, two
external interface types, one original inline helper type and the
ValidTuple definition value. Every original proof body is retained.
No new definition bundle is introduced. One supporting root retains
the complete three-theorem chain.

The consolidated DAG has 1095 nodes and 2510 edges. All 736 exact proof dependency sets across 41 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The domain restrictions are proved. Affine structure
extraction, absolute central inequalities and generic G1/G2/G3 remain open.

## Cyclic fixed points and negative affine closure

For a valid tuple at any nonzero cyclic modulus, every fibre 3*g_i=t
has at most two coordinates, including when three is not invertible.
Thus a negative affine domain has at most two fixed points and obeys
2*|S|<=n+2 under injective doubling. At odd modulus, negative affine
closure on the entire valid tuple forces n<=2. The closure assumption
is explicit; these results do not extract a large affine block from
dense represented differences.

All four cyclic fixed-point results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, three
external interface types and the ValidTuple definition value. Every
original proof body is retained. No inline helper or new definition
bundle is introduced. One supporting root retains the complete
four-theorem chain.

The consolidated DAG has 1103 nodes and 2528 edges. All 740 exact proof dependency sets across 42 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Cyclic fixed-point control is proved. Affine structure extraction, absolute
central inequalities and generic G1/G2/G3 remain open.

## Verified four-theorem cyclic fixed-point export

For a valid tuple at any nonzero cyclic modulus, every fibre 3*g_i=t
has at most two coordinates, including when three is not invertible.
Thus a negative affine domain has at most two fixed points and obeys
2*|S|<=n+2 under injective doubling. At odd modulus, negative affine
closure on the entire valid tuple forces n<=2. The closure assumption
is explicit; these results do not extract a large affine block from
dense represented differences.

All four cyclic fixed-point results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, three
external interface types and the ValidTuple definition value. Every
original proof body is retained. No inline helper or new definition
bundle is introduced. One supporting root retains the complete
four-theorem chain.

The consolidated DAG has 1103 nodes and 2528 edges. All 740 exact proof dependency sets across 42 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Cyclic fixed-point control is proved. Affine structure extraction, absolute
central inequalities and generic G1/G2/G3 remain open.

## Propagation from positive affine domains

A positive affine domain with at least seven represented neighbors
of an outside coordinate forces another positive affine map on their
images. Rich neighbor sets of distinct outside coordinates meet in
at most one point, and a rich neighbor set R in a domain S obeys
|R|+|S|<=n+1. The domain, outside-coordinate and seven-neighbor
hypotheses are explicit; a useful affine domain has not yet been
extracted from dense represented differences.

All five positive affine propagation results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify five original target types and dependency sets, three
external interface types, two original inline helper types and three
definition values. Every original proof body is retained. No new
definition bundle is introduced. Two supporting roots retain the
complete five-theorem chain.

The consolidated DAG has 1113 nodes and 2557 edges. All 745 exact proof dependency sets across 43 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Affine structure extraction, absolute central inequalities and generic G1/G2/G3 remain open.

## Verified five-theorem positive affine propagation export

A positive affine domain with at least seven represented neighbors
of an outside coordinate forces another positive affine map on their
images. Rich neighbor sets of distinct outside coordinates meet in
at most one point, and a rich neighbor set R in a domain S obeys
|R|+|S|<=n+1. The domain, outside-coordinate and seven-neighbor
hypotheses are explicit; a useful affine domain has not yet been
extracted from dense represented differences.

All five positive affine propagation results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify five original target types and dependency sets, three
external interface types, two original inline helper types and three
definition values. Every original proof body is retained. No new
definition bundle is introduced. Two supporting roots retain the
complete five-theorem chain.

The consolidated DAG has 1113 nodes and 2557 edges. All 745 exact proof dependency sets across 43 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Affine structure extraction, absolute central inequalities and generic G1/G2/G3 remain open.

## Classification of represented triangles

For any valid tuple with injective doubling, every represented triangle
lies in a positive affine domain, lies in a negative affine domain, or
has image edges {(u,v),(u,z),(w,v)} on four distinct coordinates with
2*(g(u)-g(v))=g(z)-g(w). The result is generic in the dimension and
ambient additive commutative group. It does not count the exceptional
triangles or assert that many triangles share an affine offset.

All four triangle classification results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, three
external interface types, two original inline helper types and the
ValidTuple definition value. Every original proof body is retained.
No new definition bundle is introduced. One supporting root retains
the complete four-theorem chain.

The consolidated DAG has 1121 nodes and 2576 edges. All 749 exact proof dependency sets across 44 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Large positive-domain extraction, absolute central inequalities and generic G1/G2/G3 remain open.

## Verified four-theorem triangle classification export

For any valid tuple with injective doubling, every represented triangle
lies in a positive affine domain, lies in a negative affine domain, or
has image edges {(u,v),(u,z),(w,v)} on four distinct coordinates with
2*(g(u)-g(v))=g(z)-g(w). The result is generic in the dimension and
ambient additive commutative group. It does not count the exceptional
triangles or assert that many triangles share an affine offset.

All four triangle classification results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, three
external interface types, two original inline helper types and the
ValidTuple definition value. Every original proof body is retained.
No new definition bundle is introduced. One supporting root retains
the complete four-theorem chain.

The consolidated DAG has 1121 nodes and 2576 edges. All 749 exact proof dependency sets across 44 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Large positive-domain extraction, absolute central inequalities and generic G1/G2/G3 remain open.

## Counting triangles with L-shaped images

For any valid tuple with injective doubling, a family of represented
triangles with explicit L-shaped image witnesses has at most binomial(n,2)
distinct anchor supports. The unordered repeated endpoint pair determines
the symmetric image edges and thereby recovers the anchor support. The
result is generic in the dimension and ambient additive commutative
group. Affine-domain triangle counts and large-domain extraction are
separate tasks.

All four exceptional triangle count results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, two
external interface types, two original inline helper types and the
ValidTuple definition value. Every original proof body is retained.
No new definition bundle is introduced. One supporting root retains
the complete four-theorem chain.

The consolidated DAG has 1129 nodes and 2595 edges. All 753 exact proof dependency sets across 45 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Extracting large positive domains, absolute central inequalities and generic G1/G2/G3 remain open.

## Verified four-theorem exceptional triangle count export

For any valid tuple with injective doubling, a family of represented
triangles with explicit L-shaped image witnesses has at most binomial(n,2)
distinct anchor supports. The unordered repeated endpoint pair determines
the symmetric image edges and thereby recovers the anchor support. The
result is generic in the dimension and ambient additive commutative
group. Affine-domain triangle counts and large-domain extraction are
separate tasks.

All four exceptional triangle count results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify four original target types and dependency sets, two
external interface types, two original inline helper types and the
ValidTuple definition value. Every original proof body is retained.
No new definition bundle is introduced. One supporting root retains
the complete four-theorem chain.

The consolidated DAG has 1129 nodes and 2595 edges. All 753 exact proof dependency sets across 45 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Extracting large positive domains, absolute central inequalities and generic G1/G2/G3 remain open.

## Pair and triangle counts in linear block families

For a family of coordinate subsets whose distinct members intersect
in at most one point, the total pair count is at most binomial(n,2).
If every block has size at most M, then
3*sum choose(|S|,3)<=(M-2)*choose(n,2). The formulas include empty and
small blocks and use natural subtraction. These are purely combinatorial
results, with their intersection and size hypotheses explicit.

Both linear block counting results are private and Proved. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify both original target types and dependency sets. Every original
proof body is retained. No definition bundle, inline helper or external
theorem interface is required. One supporting root retains both results.

The consolidated DAG has 1132 nodes and 2597 edges. All 755 exact proof dependency sets across 46 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Large-domain extraction, absolute central inequalities and generic G1/G2/G3 remain open.

## Verified two-theorem linear block count export

For a family of coordinate subsets whose distinct members intersect
in at most one point, the total pair count is at most binomial(n,2).
If every block has size at most M, then
3*sum choose(|S|,3)<=(M-2)*choose(n,2). The formulas include empty and
small blocks and use natural subtraction. These are purely combinatorial
results, with their intersection and size hypotheses explicit.

Both linear block counting results are private and Proved. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify both original target types and dependency sets. Every original
proof body is retained. No definition bundle, inline helper or external
theorem interface is required. One supporting root retains both results.

The consolidated DAG has 1132 nodes and 2597 edges. All 755 exact proof dependency sets across 46 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Large-domain extraction, absolute central inequalities and generic G1/G2/G3 remain open.

## Triangle counts in full affine domains

Full positive and negative affine domains at distinct offsets meet
in at most one coordinate for a valid tuple with injective doubling.
Positive domains with size bounded by M satisfy
3*sum choose(|S|,3)<=(M-2)*choose(n,2). At nonzero cyclic modulus,
negative domains satisfy 6*sum choose(|S|,3)<=(n-2)*choose(n,2).
The sums are over distinct full domains; all hypotheses are explicit.

All six affine-domain counting results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify six original target types and dependency sets, five
external interface types, two original inline helper types and three
definition values. Every original proof body is retained. One new
bundle contains the full positive and negative domains. Two supporting
roots retain all six results.

The consolidated DAG has 1145 nodes and 2626 edges. All 761 exact proof dependency sets across 47 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Large-domain extraction under an explicit missing-pair density hypothesis is verified locally. Absolute central inequalities and generic G1/G2/G3 remain open.

## Total count of represented triangles

For a valid cyclic tuple with injective doubling, let M bound every
full positive affine domain. Any represented-triangle family Ts obeys
6*|Ts|<=(2*(M-2)+(n-2)+6)*choose(n,2). The proof combines positive
and negative affine-domain triangle counts with the exceptional family
bound. The representation and domain-size hypotheses are explicit.

All three represented-triangle counting results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify three original target types and dependency sets, four
external interface types and three existing definition values. Every
original proof body is retained. No inline helper or new definition
bundle is required. One supporting root retains all three results.

The consolidated DAG has 1151 nodes and 2641 edges. All 764 exact proof dependency sets across 48 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Controlling coordinates outside large domains, absolute central inequalities and generic G1/G2/G3 remain open.

## Verified six-theorem affine-domain count export

Full positive and negative affine domains at distinct offsets meet
in at most one coordinate for a valid tuple with injective doubling.
Positive domains with size bounded by M satisfy
3*sum choose(|S|,3)<=(M-2)*choose(n,2). At nonzero cyclic modulus,
negative domains satisfy 6*sum choose(|S|,3)<=(n-2)*choose(n,2).
The sums are over distinct full domains; all hypotheses are explicit.

All six affine-domain counting results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify six original target types and dependency sets, five
external interface types, two original inline helper types and three
definition values. Every original proof body is retained. One new
bundle contains the full positive and negative domains. Two supporting
roots retain all six results.

The consolidated DAG has 1145 nodes and 2626 edges. All 761 exact proof dependency sets across 47 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Large-domain extraction under an explicit missing-pair density hypothesis is verified locally. Absolute central inequalities and generic G1/G2/G3 remain open.

## Triangle lower bound from missing coordinate pairs

A two-coordinate subset is contained in at most n-2 coordinate
triangles. Thus a family Ts containing every triangle that avoids
a pair family D satisfies choose(n,3)<=|Ts|+(n-2)*|D|. These are
purely combinatorial results, with the pair-size and coverage
hypotheses explicit.

Both missing-pair triangle counting results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify both original target types and dependency sets. Every
original proof body is retained. No definition bundle, inline helper or
external theorem interface is required. One supporting root retains
both results.

The consolidated DAG has 1154 nodes and 2643 edges. All 766 exact proof dependency sets across 49 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Absolute central inequalities and generic G1/G2/G3 remain open.

## A large positive domain from few missing pairs

For a valid nonzero cyclic tuple with injective doubling, let D be
a family of two-coordinate subsets covering every unrepresented doubled
difference pair. If n>=44 and (n-9)*|D|<3*choose(n,2), then some
offset t satisfies n<2*|positiveAffineDomain(g,t)|+40. The proof
combines triangle counts and maximizes domain size over the finite
offset group. Coverage and density remain explicit assumptions.

All three triangle density domain results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify three original target types and dependency sets, two
external interface types and three existing definition values. Every
original proof body is retained. No inline helper or new definition
bundle is required. One supporting root retains all three results.

The consolidated DAG has 1160 nodes and 2656 edges. All 769 exact proof dependency sets across 50 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

One-escape closure and the conditional sharp odd bound at n>=144 are now verified locally. The density premise remains explicit; absolute central inequalities and generic G1/G2/G3 remain open.

## Verified three-theorem represented-triangle count export

For a valid cyclic tuple with injective doubling, let M bound every
full positive affine domain. Any represented-triangle family Ts obeys
6*|Ts|<=(2*(M-2)+(n-2)+6)*choose(n,2). The proof combines positive
and negative affine-domain triangle counts with the exceptional family
bound. The representation and domain-size hypotheses are explicit.

All three represented-triangle counting results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify three original target types and dependency sets, four
external interface types and three existing definition values. Every
original proof body is retained. No inline helper or new definition
bundle is required. One supporting root retains all three results.

The consolidated DAG has 1151 nodes and 2641 edges. All 764 exact proof dependency sets across 48 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Controlling coordinates outside large domains, absolute central inequalities and generic G1/G2/G3 remain open.

## Verified two-theorem missing-pair triangle count export

A two-coordinate subset is contained in at most n-2 coordinate
triangles. Thus a family Ts containing every triangle that avoids
a pair family D satisfies choose(n,3)<=|Ts|+(n-2)*|D|. These are
purely combinatorial results, with the pair-size and coverage
hypotheses explicit.

Both missing-pair triangle counting results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify both original target types and dependency sets. Every
original proof body is retained. No definition bundle, inline helper or
external theorem interface is required. One supporting root retains
both results.

The consolidated DAG has 1154 nodes and 2643 edges. All 766 exact proof dependency sets across 49 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Absolute central inequalities and generic G1/G2/G3 remain open.

## Neighbors outside a full positive affine domain

[Full positive domain neighbors](FullPositiveDomainNeighbors.md)
specializes affine propagation to full domains. An outside coordinate
has at most six represented neighbors, or its neighbor set plus the
domain has size at most n+1. Rich neighbor sets from distinct outside
coordinates meet in at most one point. Their missing counts satisfy
|S|<=d_a+d_b+6. Four original proofs, eight exact declaration types
and two existing definition values pass both revisions. Counting and
averaging the missing incidences remains; the one-escape conclusion,
absolute central inequalities and generic G1/G2/G3 remain open.
Split export and private publication remain.

## Missing incidences and averaged pair deficits

[Cross-pair deficit counts](CrossPairDeficit.md) proves two finite
counting lemmas. Missing incidences between disjoint sides inject into
any unordered-pair family covering them. If M<=d_a+d_b+C for every
distinct pair in a set A of size at least two, then
|A|*M<=2*sum_a d_a+C*|A|. Both original proofs and exact types pass
both revisions. No definitions or group hypotheses are needed.
The one-escape conclusion, absolute central inequalities and generic
G1/G2/G3 remain open. Split export and private publication remain.

## Arithmetic for the dense domain complement

[Dense complement arithmetic](DenseDomainComplementArithmetic.md)
proves three scalar consequences of (n-9)*D<3*choose(n,2) at n>=144.
First 5*D<8*n. For M+r=n and n<2*M+40, the averaged bound
r*M<=2*D+6*r when r>=2 forces r<=12. Then r*M<=D+13*r forces
r<=1. All three original proofs and exact types pass both revisions.
Connecting the explicit scalar premises to a full affine domain remains.
Absolute central inequalities and generic G1/G2/G3 remain open.
Split export and private publication remain.

## Verified three-theorem triangle density domain export

For a valid nonzero cyclic tuple with injective doubling, let D be
a family of two-coordinate subsets covering every unrepresented doubled
difference pair. If n>=44 and (n-9)*|D|<3*choose(n,2), then some
offset t satisfies n<2*|positiveAffineDomain(g,t)|+40. The proof
combines triangle counts and maximizes domain size over the finite
offset group. Coverage and density remain explicit assumptions.

All three triangle density domain results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify three original target types and dependency sets, two
external interface types and three existing definition values. Every
original proof body is retained. No inline helper or new definition
bundle is required. One supporting root retains all three results.

The consolidated DAG has 1160 nodes and 2656 edges. All 769 exact proof dependency sets across 50 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

One-escape closure and the conditional sharp odd bound at n>=144 are now verified locally. The density premise remains explicit; absolute central inequalities and generic G1/G2/G3 remain open.

## One-escape structure from few missing pairs

[Dense positive domain one-escape](DensePositiveDomainOneEscape.md)
proves that, for a valid nonzero cyclic tuple with injective doubling
and n>=144, an explicit pair cover D with
(n-9)*|D|<3*choose(n,2) forces an actual one-escape affine doubling
closure. Triangle counts give a large domain; missing-incidence counting
and neighbor bounds show its complement has size at most one. Three
original proofs, twelve exact declaration types and two existing
definition values pass both revisions. Applying AlmostDoubling remains.
The density premise is explicit; other tuples, absolute central
inequalities and generic G1/G2/G3 remain open. Split export and private
publication remain.

## Sharp odd modulus bound from few missing pairs

[Dense-pair modulus bound](DensePairModulusBound.md) proves
2^n-1<=N for a valid odd tuple at n>=144 whenever an explicit
pair cover D of the unrepresented doubled differences satisfies
(n-9)*|D|<3*choose(n,2). The proof applies AlmostDoubling to the
extracted one-escape structure. Conversely, any smaller odd-modulus
counterexample must have 3*choose(n,2)<=(n-9)*|D| for every such D.
Both original proofs, six exact declaration types and the ValidTuple
value pass both revisions. The sparse represented-pair regime, lower
dimensions, absolute central inequalities and generic G1/G2/G3 remain
open. Split export and private publication remain.

## Dense positive-domain proof chain

For a valid tuple of length n>=144 at odd modulus N, let D be a family
of two-coordinate subsets covering every unrepresented doubled coordinate
difference. If (n-9)*|D|<3*choose(n,2), then 2^n-1<=N. The density
premise is explicit. The proof obtains a large full positive affine
domain, bounds its complement by one, and applies AlmostDoubling.

Any remaining odd counterexample at n>=144 must satisfy
3*choose(n,2)<=(n-9)*|D| for every such pair cover. This argument does
not cover n<144; existing small-dimension results remain valid. The sparse
represented-pair regime, absolute central inequalities and unrestricted
G1/G2/G3 remain open.

The fourteen original proofs are in five source modules:

* FullPositiveDomainNeighbors.lean: four domain-map and neighbor bounds.
* CrossPairDeficit.lean: two incidence and averaging bounds.
* DenseDomainComplementArithmetic.lean: three scalar density implications.
* DensePositiveDomainOneEscape.lean: three actual one-escape extraction results.
* DensePairModulusBound.lean: the sharp odd bound and necessary counterexample density.

All fourteen results are private and Proved on Prove2Me. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify fourteen original target types and dependency sets, four external
interface types, one original inline helper type and two existing
definition values. All original proof bodies are retained. No new
definition bundle is required. One terminal root retains all fourteen
results, including the conditional sharp odd bound and its necessary
counterexample-density consequence.

The consolidated DAG has 1184 nodes and 2709 edges. All 783 exact proof dependency sets across 51 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The density premise remains explicit. The sparse represented-pair regime, absolute central inequalities and unrestricted G1/G2/G3 remain open.

## Nonuniform translated-support packing

[Nonuniform translated packing](NonuniformTranslatedPacking.md) extends
permutation packing to equal-value disjoint pairs of varying support
sizes and fixed cardinality gap. If each natural weight times its
support binomial coefficient is at most M, the total weight is at most M.
With injective doubling, the union determines a pair at fixed first-side
cardinality, giving a second bound choose(|A|,2*j) for balanced pairs
of side size j. Four original proofs, ten exact declaration types and
two existing definition values pass both revisions. No new definition
is introduced. The arbitrary-degree match decomposition and numerical
central bounds remain; unrestricted G1/G2/G3 remain open. Split export
and private publication remain.

## Exact squarefree translation counts from disjoint cores

[Squarefree translation core counts](SquarefreeTranslationCoreCount.md)
proves an exact formula in every degree: each match decomposes uniquely
into disjoint equal-size difference supports (U,V) and a common subset
outside their union. The match count is the sum over cores of
choose(|A|-2*|U|,k-|U|). Validity then allows nonuniform weighted packing
to bound this count through explicit support-binomial products. Four
original proofs, nine exact declaration types and three definition values
pass both revisions. One new generic core definition is introduced.
The numerical central bounds and unrestricted G1/G2/G3 remain open.
Split export and private publication remain.

## Nonuniform translation packing and exact core counts

Eight generic lemmas combine nonuniform translated-support packing with
an exact arbitrary-degree count of squarefree translation matches.

For disjoint equal-evaluation pairs with fixed cardinality gap, separating
permutation events are disjoint even when support sizes vary. Natural
weights w satisfying w*choose(|U|+|V|,|U|)<=M therefore have sum at most M.
With injective doubling, a fixed union determines a pair of prescribed
first-side size and signed value; a balanced size-j family supported in A
has at most choose(|A|,2*j) members.

Every degree-k translation match decomposes uniquely into disjoint
differences U,V and a common support H outside their union. Thus

    |matches| = sum_(U,V) in cores choose(|A|-2*|U|,k-|U|).

This identity needs no validity assumption. For valid tuples, any M
bounding choose(|A|-2*j,k-j)*choose(2*j,j) at every core size present
bounds the match count. This numerical premise is explicit; sufficient
central-degree estimates and unrestricted G1/G2/G3 remain open.

The original proofs are in NonuniformTranslatedPacking.lean and
SquarefreeTranslationCoreCount.lean. The new definition bundle contains
the original separating-permutation event definition (previously inline)
and the new squarefreeTranslationCores definition.

All eight results are private and Proved on Prove2Me. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify eight original target types and dependency sets, three external
interface types, eight original inline helper types and four definition
values. All original proof bodies are retained. One new definition bundle
contains the separating-event and disjoint-core definitions. Two supporting
roots retain the support-union cap and the final weighted match bound.

The consolidated DAG has 1200 nodes and 2744 edges. All 791 exact proof dependency sets across 52 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The numerical core-weight premise remains explicit. Sufficient central-degree estimates and unrestricted G1/G2/G3 remain open.

## Squarefree translation counts grouped by core rank

[Squarefree translation core ranks](SquarefreeTranslationCoreRanks.md)
groups the exact arbitrary-degree match count over any finite cover of
the core sizes. For valid tuples, each size-j core family is bounded by
choose(2*j,j); injective doubling also bounds it by choose(|A|,2*j).
The common-support weights can be summed against the minimum of both
caps. Nonzero translations have no empty core, so their explicit bound
starts at j=1. Six original proofs, thirteen exact declaration types
and three existing definition values pass both revisions. No definition
is introduced. These estimates do not yet establish the central bounds;
unrestricted G1/G2/G3 remain open. Split export and publication remain.

## Fractional packing and combined core-rank certificates

[Nonuniform fractional translation bounds](NonuniformTranslationFractional.md)
normalizes the separating-permutation count over the rationals: the sum
of reciprocal support-binomial numbers is at most one. Grouped by core
size, this gives sum_j c_j/choose(2*j,j)<=1. A rational certificate with
alpha>=0, beta_j>=0 and common-support weight w_j<=alpha/choose(2*j,j)+beta_j
therefore bounds the match count by alpha+sum_j C_j*beta_j, where
C_j=min(choose(2*j,j),choose(|A|,2*j)). This combines the shared packing
budget and rank caps without discarding either. Four original proofs,
fourteen exact declaration types and four existing definition values
pass both revisions. No new definition is introduced. The certificate
premises and sufficient central-degree estimates remain to be supplied;
unrestricted G1/G2/G3 remain open. Split export and publication remain.

## Core-rank bounds and fractional certificates

Ten generic lemmas group translation cores by size and combine two
independent cardinality caps with one shared fractional packing bound.
If c_j is the number of size-j cores supported in A, validity gives
c_j<=choose(2*j,j), while injective doubling gives c_j<=choose(|A|,2*j).
The exact match count is sum_j c_j*choose(|A|-2*j,k-j). Nonzero
translations have no empty core, so their ranks begin at one.

The shared rational inequality is sum_j c_j/choose(2*j,j)<=1. Thus
any alpha>=0 and beta_j>=0 with

    choose(|A|-2*j,k-j) <= alpha/choose(2*j,j)+beta_j

give the match-count bound

    |matches| <= alpha + sum_j min(choose(2*j,j),choose(|A|,2*j))*beta_j.

Every sum is over an explicit finite cover of the core ranks. The
certificate hypotheses are explicit; no certificate sufficient for the
central-degree goal is supplied. Unrestricted G1/G2/G3 remain open.
The original proofs are in SquarefreeTranslationCoreRanks.lean and
NonuniformTranslationFractional.lean.

All ten results are private and Proved on Prove2Me. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify ten original target types and dependency sets, five external
interface types, seven original inline helper types and four existing
definition values. All original proof bodies are retained. No new
definition bundle is needed. Two supporting roots retain the explicit
positive-rank bound and the combined fractional certificate.

The consolidated DAG has 1220 nodes and 2794 edges. All 801 exact proof dependency sets across 53 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The numerical certificate premises remain explicit. Sufficient central-degree estimates and unrestricted G1/G2/G3 remain open.

## A uniform limitation of the core-rank certificate

[Translation rank-certificate barrier](TranslationRankCertificateBarrier.md)
proves a symbolic limitation of the current numerical relaxation. If
rank two is allowed at support size2*k with k>=3, every nonnegative
beta certificate has objective at least6*choose(2*k-4,k-2), hence at
least three eighths of choose(2*k,k). This is a certificate-objective
lower bound; it does not assert that the abstract profile is realized
by a valid tuple. Four original proofs and four exact types pass both
revisions with standard axioms. No new definitions or finite exclusion
campaigns are involved. Stronger small-core compatibility or aggregate
control across anchor pairs is still needed; G1/G2/G3 remain open.
These results are included in the seven-theorem chain, now private and Proved.

## Quartic growth inside a hypothetical large odd counterexample

[Odd-counterexample quartic bound](OddCounterexampleQuarticBound.md)
connects the proved dense-case obstruction to the earlier quadratic
incidence count. For n>=144, any valid odd-modulus tuple with N<2^n-1
must obey (n-9)*|E|<=(n-12)*choose(n,2), where E is the disjointly
represented doubled-difference pair family. It therefore satisfies
|repeatedCoinCover(g,4)|>=choose(n+1,2)+choose(n,3). The counterexample
premise stays explicit; this does not establish the higher central
inequalities. Three original proofs, eight exact declaration types and
three existing definition values pass both revisions. Generic G1/G2/G3
remain open. These results are included in the seven-theorem chain, now private and Proved.

## Counterexample growth constraints and certificate limits

Seven generic results record a restriction on the numerical certificate
method and a necessary growth condition inside any large odd counterexample.

If rank two is permitted at support size 2*k with k>=3, the fractional
certificate objective is at least 6*choose(2*k-4,k-2), hence at least
three eighths of choose(2*k,k). This is a limitation of the relaxation;
no realization of its abstract profile by a valid tuple is asserted.

For any valid odd-modulus tuple with n>=144 and N<2^n-1, the dense-case
obstruction forces (n-9)*|E|<=(n-12)*choose(n,2), where E consists of
anchor pairs with disjoint coordinate representations of their doubled
differences. The earlier quadratic-count theorem then yields

    |repeatedCoinCover(g,4)| >= choose(n+1,2)+choose(n,3).

The counterexample premise remains explicit. This quartic consequence
does not establish the higher central-degree inequalities; generic
G1/G2/G3 remain open. The original proofs are in
TranslationRankCertificateBarrier.lean and OddCounterexampleQuarticBound.lean.

All seven results are private and Proved on Prove2Me. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify seven original target types and dependency sets, two external
interface types and three existing definition values. All original proof
bodies are retained. No new definition bundle or inline helper is needed.
Two supporting roots retain the certificate floor and the hypothetical
counterexample quartic-growth consequence.

The consolidated DAG has 1231 nodes and 2816 edges. All 808 exact proof dependency sets across 54 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The numerical certificate premises remain explicit. Sufficient central-degree estimates and unrestricted G1/G2/G3 remain open.

## Full recursive decomposition of repeated coin values

[Squarefree-double decomposition](SquarefreeDoubleCoinDecomposition.md)
includes every multiplicity pattern at arbitrary degree. Each multiset
has a unique squarefree remainder S and a halved multiset t. Consequently,
C_k is the union of sum(S)+2*C_r over |S|+2*r=k, and D_k is exactly the
same union with r>=1. At odd modulus every fixed S layer has |C_r| values.
Seven original proofs, ten exact declaration types and two existing
definition values pass both revisions. Distinct layers can overlap;
bounding that overlap sufficiently for the central inequalities remains
open. Generic G1/G2/G3 remain open. The seven results are now private and Proved on Prove2Me.

## Full squarefree-double coin decomposition on Prove2Me

Seven generic results provide a complete recursive decomposition of coin
values in every degree. Each coordinate multiset is uniquely a squarefree
remainder S plus two copies of a halved multiset t. Hence

    C_k = union_(r=0,...,floor(k/2), |S|=k-2*r) (sum g(S) + 2*C_r),
    D_k = union_(r=1,...,floor(k/2), |S|=k-2*r) (sum g(S) + 2*C_r).

Here C_k includes every degree-k coin representation and D_k includes
those with a repeated coordinate. The identities require neither tuple
validity nor oddness. At odd modulus each fixed-S layer has exactly
|C_r| values. Uniqueness is for coordinate multisets, not their values;
distinct value layers can overlap. Bounding this full union sufficiently
at both central degrees remains open, as do generic G1/G2/G3.
The original proofs are in SquarefreeDoubleCoinDecomposition.lean.

All seven results are private and Proved on Prove2Me. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify seven original target types and dependency sets, one original
inline helper type and two existing definition values. Exact parser spans
retain every original proof body. No new definition bundle or external
theorem interface is required. Four supporting roots retain multiset
uniqueness, both complete union identities, and fixed-layer cardinality.

The consolidated DAG has 1242 nodes and 2835 edges. All 815 exact proof dependency sets across 55 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Different layers can overlap. The central-degree union lower bounds and generic G1/G2/G3 remain open.

## Exponential overlap of full central-degree layers

[Many squarefree-double layers](ManySquarefreeDoubleLayers.md) proves
that independent pairs of doubling relations can produce exponentially
many squarefree remainders for one coin value. For every m>=1, the valid
Mersenne power tuple of length n=6*m has a repeated value at central
degree k=3*m lying in at least 2^m distinct layers sum g(S)+2*C_m, with
|S|=m. This is a symbolic family for arbitrary m, not a finite search.
The modulus is the sharp odd example 2^(6*m)-1, so the result is not a
counterexample to min-modulus. A useful lower bound on the full union must
handle large individual overlaps. Two original proofs, twelve exact types
and six existing definition values pass both revisions. Generic central
inequalities and G1/G2/G3 remain open. Both results are now private and Proved on Prove2Me.

## Verified exponential central-layer overlap

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

## Exact coin counts under affine doubling closure

[Closed doubling coin counts](ClosedDoublingCoinCounts.md) proves that
if 2*A=A+b for the coordinate set A, then D_(k+2)=C_(k+1)+b
in every degree. For a valid tuple this gives |C_d|+1=sum_(j<=d)choose(n,j)
and |D_d|+1=sum_(j<d)choose(n,j) for every d>=1. The full repeated
cover is counted with all multiplicity patterns and overlaps. Closure
is an explicit hypothesis; the modulus bound for this class was already
known. Five original proofs, eleven exact types and three existing
definition values pass both revisions. General central inequalities
and G1/G2/G3 remain open. All five results are now private and Proved on Prove2Me.

## Exact Mersenne counts in every positive degree

[Exact Mersenne coin counts](MersenneExactCoinCounts.md) proves that
for every n>=1 the valid power tuple modulo 2^n-1 is closed under
doubling and has |C_d|+1=sum_(j<=d)choose(n,j) and
|D_d|+1=sum_(j<d)choose(n,j) for every d>=1. These full counts
include all multiplicity patterns and remain exact despite the previously
proved exponential layer overlap at central degrees n=6*m. No finite
enumeration is used. Two original proofs, fourteen exact types and six
existing definition values pass both revisions. The uniform central
inequality for arbitrary valid tuples and G1/G2/G3 remain open.
Both results are now private and Proved on Prove2Me.

## Exact closed-doubling coin counts on Prove2Me

Five generic results give exact full-degree coin-cover counts under the
explicit set equality 2*A=A+b, where A is the coordinate set and 2*A
means its dilation by two. In every degree, D_(k+2)=C_(k+1)+b, so
|D_(k+2)|=|C_(k+1)|. This equality needs neither validity nor oddness.

For a valid tuple of length n, squarefree/repeated separation gives

    |C_d|+1 = sum_(j=0,...,d) choose(n,j),
    |D_d|+1 = sum_(j=0,...,d-1) choose(n,j),  for every d>=1.

This counts the full repeated cover with all multiplicity patterns and
overlaps. The central target is attained exactly throughout this class.
Earlier work already proves the modulus bound under this structural
hypothesis; these results add exact degree-by-degree cover counts.
Closure is not inferred for arbitrary valid tuples. Generic central
inequalities and G1/G2/G3 remain open.
The original proofs are in ClosedDoublingCoinCounts.lean.

All five results are private and Proved on Prove2Me. Verified submissions
and exact server proof-source readbacks pass. Both revisions verify five
original target types and dependency sets, two external theorem interfaces
and three existing definition values. Nine exact original inline helper
types and the inline subset-sum definition value also agree. Exact parser
spans retain every original proof body. No new definition bundle is required.
One supporting root retains the full exact-count chain.

The consolidated DAG has 1254 nodes and 2867 edges. All 822 exact proof dependency sets across 57 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The central-degree union lower bounds and generic G1/G2/G3 remain open.

## Exact Mersenne coin counts on Prove2Me

Two results realize the exact full-degree coin counts in every sharp
Mersenne power tuple. For every n>=1, put N=2^n-1 and g_i=2^i modulo N.
The coordinate set is fixed by doubling, including the cyclic carry.
The tuple is valid and, for every d>=1,

    |C_d|+1 = sum_(j=0,...,d) choose(n,j),
    |D_d|+1 = sum_(j=0,...,d-1) choose(n,j).

Here C_d includes all degree-d representations and D_d includes values
with a repeated-coordinate representation. The counts are exact even
beyond central degrees, and use no finite enumeration. They apply the
closed-doubling count chain, existing canonical validity and an existing
cyclic predecessor lemma, with the singleton case handled directly.

For n=6*m this combines with the previously proved exponential layer
overlap: large individual overlaps coexist with exactly sharp full-union
counts. The formula concerns the known extremal family. The uniform
central inequality for arbitrary valid tuples and G1/G2/G3 remain open.
The original proofs are in MersenneExactCoinCounts.lean.

Both results are private and Proved on Prove2Me. Verified submissions
and exact server proof-source readbacks pass. Both revisions verify two
original target types and dependency sets, six external theorem interfaces
and six existing definition values. Exact parser spans retain both original
proof bodies. No inline helper or new definition bundle is required.
One supporting root retains the entire exact Mersenne count family.

The consolidated DAG has 1258 nodes and 2884 edges. All 824 exact proof dependency sets across 58 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The central-degree union lower bounds and generic G1/G2/G3 remain open.

## CR1 — draft central repeated-cover target

CR1 is an explicitly unproved sufficient target for G2. For every valid
tuple at positive odd modulus and either central degree k>=4, prove

    |D_k|+1 >= sum_(j<k) choose(n,j),

where D_k includes every repeated-coordinate representation. No affine
closure, density condition or overlap cap is assumed. Lean checks on both
revisions establish that the statement's entire quantified type matches
the premise of the already proved G2 sufficiency theorem
1971fd39-22d6-4f56-acbb-64fa3209b49f. This is a statement check, not a proof.

CR1 is private and Open on Prove2Me, with an exact statement readback and
an attached research milestone. No CR1 solution has been submitted.
Theorem ID: 06a6b75d-6df1-4976-ae05-72ff1e7fc854
Milestone ID: 500f994a-6a1e-4cd4-8aa1-e183f116b1f9

The consolidated DAG has 1259 nodes, 2885 edges and 79 roots. Its four open leaves comprise the unchanged three core gates G1/P6, G2/From7 and G3/From7 plus CR1. All 824 exact proof dependency sets across 58 proved bundles still match; the new Open target adds no proved theorem. Alternative routes to the core gates remain available.

## Frobenius-stable interpolation still needs a cyclic orbit

[Frobenius-stable cubic interpolation](FrobeniusStableCubicInterpolation.md)
constructs six distinct torus points in characteristic two, closed under
squaring, whose unit-weight evaluations extract every cubic squarefree
coefficient. They cannot be a single full multiplicative cyclic orbit,
even after reordering. Five original proofs, nine exact declaration types
and two definition values pass both revisions. The GF(4) instance rules
out an unrestricted seven-point bound with Frobenius stability; it does
not refute CR1, a 2^n-2 point bound, or min-modulus. G1/G2/G3 and CR1 remain
open. Split export and private publication remain.
