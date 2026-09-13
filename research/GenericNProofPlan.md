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

[QuarticFibreHalfBound.lean](QuarticFibreHalfBound.lean) proves that every
quartic single-repeat fibre has at most floor(n/2) anchors. This uniform
local collision bound is available, but does not supply the global rank
or cardinality inequality.

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

[Odd cyclic extensions](ValidTupleOddExtension.md) proves that every
valid tuple at odd cyclic order embeds into a valid tuple in every
larger dimension, preserving original coordinates by an index embedding
and an injective additive homomorphism. A large new cyclic factor forces
the adjoined coordinate to have multiplicity one, and the Chinese
remainder equivalence restores a cyclic ambient group. All three proofs
pass both revisions with four exact types and one definition value.
This preserves additive obstructions but may enlarge the modulus greatly;
it does not preserve N<2^n-1. The diagonal-probe application is still
being formalized. Generic G1/G2/G3 remain open. Platform export remains.

## Diagonal probes fail in every dimension at least four

[The diagonal obstruction](DiagonalProbeObstruction.md) proves that
valid odd cyclic tuples in every dimension 4+r can contain a cubic
coefficient invisible to every diagonal weighted probe outside 2 C_2.
The fixed verified control supplies three doubled-pair identities;
additive transport and the generic extension preserve them. A nonzero
kernel vector refutes exactly the coefficient-recovery hypothesis over
any nontrivial semiring. All four proof bodies pass both revisions,
with nine exact types, five definition values and standard axioms.
No new finite search is used. Full matrices, central repeated-sum
bounds and generic G1/G2/G3 remain open. The modulus may be large;
this gives no min-modulus counterexample. Platform export remains.

## Verified eight-node diagonal-obstruction export

The three odd cyclic extension lemmas, existing control-validity theorem,
and four diagonal obstruction results have a verified split export.
Both revisions pass eight exact original types and dependency sets,
five definition values and the original bounded control helper type.
Every original theorem and helper body is retained. One control definition
bundle is added; existing probe definitions are reused. Two supporting
roots retain the entire chain. Metadata and live preflight pass.
These nodes have not yet been uploaded. Full-matrix coefficient recovery,
central repeated-sum bounds and generic G1/G2/G3 remain open.
