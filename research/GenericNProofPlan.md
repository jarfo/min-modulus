# Generic-n proof priority

The objective remains the min-modulus conjecture for arbitrary n. Generic
G1, G2 and G3 are all open. The local seventh odd dimension is proved;
no further finite enumeration is planned. The maintained Prove2Me main
frontier remains G1/P6, G2/From7 and G3/From7.

For a valid tuple g:Fin n -> ZMod N with N odd, let C_d be all d-coin
values and D_d the values admitting a repeated coordinate. The current
weaker sufficient target for G2 is the pair of absolute central bounds

    |D_k| + 1 >= sum_{j<k} binomial(n,j),
    k = floor(n/2) and k = ceil(n/2).

[AbsoluteRepeatedCoinBounds.lean](AbsoluteRepeatedCoinBounds.lean) proves
that these two inequalities imply N>=2^n-1 for n>=2. They hold through
degree three, so every odd counterexample must fail one of them at a
central degree k>=4. These are proved reductions; the required uniform
central inequalities remain open.

A concrete first step is the absolute quartic bound

    |D_4| >= binomial(n+1,2) + binomial(n,3).

[WeightedProbeLinearRank.lean](WeightedProbeLinearRank.lean) proves this
from injectivity of one matrix-weighted cubic probe outside 2*C_2,
over any coefficient field. Symbolic matrix entries are therefore
permitted. Existence of such an injective matrix remains unproved.
Joint recovery by all separate probes does not establish it. In higher
degrees, the current probe criterion also lacks some binomial terms
needed by the central target. Proving only the quartic case would not
settle generic G2.

[DiagonalProbeObstruction.lean](DiagonalProbeObstruction.lean) rules out
diagonal matrices in every dimension at least four, over every
nontrivial coefficient semiring. Full-matrix recovery requires an
argument using off-diagonal entries; changing the field alone does not
repair diagonal probes. This obstruction does not bound the modulus
and is not a counterexample to min-modulus.

[WeightedProbeContractions.lean](WeightedProbeContractions.lean) gives
an exact factorization into matrix contractions and residue grouping.
An injective matrix preserves every positive-degree coefficient through
the first stage, over any semiring. The open task is to make the second
stage, restricted outside the doubled cover, preserve that contraction
image for some full matrix. This is not implied by matrix invertibility.

[TranslatedSquarefreePacking.lean](TranslatedSquarefreePacking.lean)
bounds translated squarefree pair-sum intersections by six whenever the
shift is not a coordinate difference. More generally, exclusion from
k-support differences bounds the next-degree intersection by
binomial(2k+2,k+1), in every additive commutative group. For quartic
counting, anchor pairs whose doubled difference is a coordinate difference
remain the exception that needs control. This does not yet give the
absolute quartic or central bounds.

[CoordinateDifferencePacking.lean](CoordinateDifferencePacking.lean)
complements this with the coordinate-difference case: squarefree pair
sums on allowed coordinates A meet their translate by g_p-g_q in at
most |A|-1 values, and in no values if p or q is absent. This uses
validity and injective doubling. For pure quartic collisions the
residual supports avoid both anchors, so endpoint exclusion and an
n-3 bound can now be applied. The global count remains open.

[CoordinateDifferenceRecursion.lean](CoordinateDifferenceRecursion.lean)
now proves the exact all-degree formula
I_(k+1)(A,g_p-g_q)=binomial(|A|-2,k)+I_k(A without {p,q},2(g_p-g_q)).
It deletes two coordinates and lowers the degree by one, preserving the
central-degree relation. Both endpoint exclusion and the recurrence hold
in every additive commutative group. The next task is to control the
residual doubled shift, which need not be a coordinate difference among
the remaining coordinates. The central bounds are still unproved.

[QuarticFibreHalfBound.lean](QuarticFibreHalfBound.lean) proves that every
quartic single-repeat fibre has at most floor(n/2) anchors. This uniform
local collision bound is available, but does not supply the global rank
or cardinality inequality.

[SingleRepeatDifferenceTransport.lean](SingleRepeatDifferenceTransport.lean)
constrains doubled coordinate differences inside a whole single-repeat
fibre in every residual degree. Their representing endpoints lie outside
the entire anchor set R. Represented ordered pairs inject into distinct
ordered pairs outside R; a fibre whose every pair is represented has
|R|<=n-|R| when |R|>=2. These are collision constraints, with the full
representation hypothesis explicit in the last bound. The global
repeated-value count and central inequalities remain open.

[SingleRepeatIncidenceBounds.lean](SingleRepeatIncidenceBounds.lean)
globalizes midpoint escape counts and expresses the unresolved loss as a
sum of anchor-pair collisions. Each common-value set injects into a
restricted translated squarefree intersection. All six results are
verified on Prove2Me. Uniform control of the total loss, especially for
dense represented doubled differences, and the absolute central bounds
remain open.

[QuarticCollisionBounds.lean](QuarticCollisionBounds.lean) proves a
quantitative quartic criterion: for n>=14 at odd modulus, if the number
C of disjointly represented doubled-difference anchor pairs satisfies
3*(n-9)*C<=2*(n-14)*choose(n,2), then
|D4|>=choose(n+1,2)+choose(n,3). All six results and the exceptional-pair
definition are verified on Prove2Me. The condition is explicit; dense
exceptional cases and the higher central bounds remain open.

[SingleRepeatQuadraticCount.lean](SingleRepeatQuadraticCount.lean)
proves 2*incidences<=3*occupied_values+pair_collisions in every degree.
For n>=12 at odd modulus, the weaker explicit condition
(n-9)*C<=(n-12)*choose(n,2) now suffices for the absolute quartic count.
The four results are verified on Prove2Me. The remaining large-n
quartic case has only O(n) nonexceptional pairs; extracting sufficient
structure from this density is unproved. Higher central bounds and
generic G1/G2/G3 remain open.

[NegativeAffineBlock.lean](NegativeAffineBlock.lean) restricts partial
negative affine doubling maps: a nonfixed image cannot remain in the
domain, and 2*|S|<=n+|fixed points in S|. All three results are verified
on Prove2Me. The fixed-point term is explicit; extracting a large affine
block from represented-difference density is still unproved.

[CyclicNegativeAffineBlock.lean](CyclicNegativeAffineBlock.lean) removes
the fixed-point term for cyclic groups: a triple fibre has at most two
valid coordinates, even when three is not invertible. Therefore
2*|S|<=n+2 for a negative affine domain under injective doubling, and
full negative affine closure at odd modulus forces n<=2. All four results
are verified on Prove2Me. Affine structure extraction from dense pair
relations and the absolute central inequalities remain open.

[PositiveAffinePropagation.lean](PositiveAffinePropagation.lean) proves
that seven represented neighbors of an outside coordinate in a positive
affine domain induce a positive affine map on their images. Distinct
outside coordinates have rich neighbor sets meeting in at most one
point, and a rich neighbor set R in S obeys |R|+|S|<=n+1. All five
results are verified on Prove2Me. Existence of a useful domain and the
absolute central inequalities remain open.

[TriangleDifferencePatterns.lean](TriangleDifferencePatterns.lean)
classifies every represented doubled-difference triangle as positive
affine, negative affine, or an L-shaped image on four distinct
coordinates. All four results are verified on Prove2Me. Extracting large positive domains remains open,
as are the absolute central inequalities.

[ExceptionalTriangleCount.lean](ExceptionalTriangleCount.lean) proves
that any family of represented triangles with explicit L-shape witnesses
has at most binomial(n,2) distinct anchor supports. All four results are
verified on Prove2Me. Extracting large positive domains remains open, as do the absolute central
inequalities.

[LinearBlockTriangleCount.lean](LinearBlockTriangleCount.lean) proves
pair and triangle counts for families whose distinct blocks meet in at
most one coordinate. Both results are verified on Prove2Me. Extracting large domains and the
absolute central inequalities remain open.

[AffineDomainTriangleCounts.lean](AffineDomainTriangleCounts.lean)
defines full positive and negative affine domains and bounds their
triangle counts. All six results and both definitions are verified on
Prove2Me. Large-domain extraction under an explicit missing-pair density
hypothesis is verified locally; absolute central inequalities remain open.

[RepresentedTriangleCounts.lean](RepresentedTriangleCounts.lean)
assembles the total represented-triangle upper bound from the affine
and exceptional families. All three results are verified on Prove2Me.
Controlling coordinates outside large positive domains and the absolute
central inequalities remain open.

[MissingPairTriangleCount.lean](MissingPairTriangleCount.lean) bounds
the number of triangles lost to a family of missing pairs. Both results
are verified on Prove2Me. The pair-size and coverage hypotheses are
explicit; absolute central inequalities remain open.

[TriangleDensityDomainBound.lean](TriangleDensityDomainBound.lean)
extracts a full positive affine domain of roughly half the coordinates
under explicit missing-pair coverage and density assumptions. All three
results are verified on Prove2Me. One-escape closure and the conditional sharp odd bound at n>=144
are verified locally. Absolute central inequalities remain open.

The stronger successive-growth route remains available. For d>=2,
[RepeatedCoinGrowth.lean](RepeatedCoinGrowth.lean) proves
D_d = 2*A + C_(d-2) and |C_d| = binomial(n,d) + |D_d|. The inequalities
|D_d|>=|C_(d-1)| are proved at d=2,3; proving them for d>=4 and
2d<=n+1 would also settle G2. Neither route discharges G1 or G3.

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

The two reusable G3 compatible-family statements are now accepted on
Prove2Me and connected through two supporting roots. The consolidated
DAG has 866 nodes; its three generic open leaves are unchanged.

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

All five higher-translate statements are now accepted on Prove2Me and
connected through their terminal growth implication. The consolidated
DAG has 876 nodes and 1982 edges; all 621 exact proof dependency
sets match, and its three generic open leaves are unchanged.

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
