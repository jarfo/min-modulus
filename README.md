# Minimum modulus for the unique multiset-sum problem

[![Lean CI](https://github.com/jarfo/min-modulus/actions/workflows/build.yml/badge.svg)](https://github.com/jarfo/min-modulus/actions/workflows/build.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

This repository is the Lean 4 formalization accompanying the paper

> José A. R. Fonollosa, *Minimum modulus for the unique multiset-sum problem*,
> [arXiv:2607.08366](https://arxiv.org/abs/2607.08366), 2026.

The code in this repository is licensed under the Apache License 2.0; see [LICENSE](LICENSE).

The main theorem of the paper is kernel-checked end-to-end: `nmin_eq` builds
with **0 errors, 0 sorries** and uses only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`, checked with `#print axioms nmin_eq`).

The repository also formalizes Proposition 2 of the paper (optimality among
elementary abelian $`2`$-groups): if $`g_0, \dots, g_{n-1} \in (\mathbb{Z}_2)^k`$
have unique multiset sums, then $`k \ge n - 1`$, so the least such group has
order $`2^{n-1}`$. See [Proposition 2](#proposition-2-elementary-abelian-2-groups)
below (also 0 sorries, standard axioms only).

Finally, the repository formalizes the resolution of **open problem 4** of the
paper — the exact minimum order for unique multiset sums over *all* finite
abelian groups — following

> Michael Inal, *The Exact Minimum Order for Unique Multiset Sums in Finite
> Abelian Groups*, [OSF preprint](https://doi.org/10.17605/OSF.IO/C58Q9), 2026.

The answer is $`m_{\mathrm{ab}}(n) = 2^{n-1}`$: a lower bound valid over every
finite abelian group (not just elementary abelian ones), matched by the
elementary abelian construction, with a classification of the extremal case.
See [Open problem 4](#open-problem-4-all-finite-abelian-groups) below (0
sorries, standard axioms only).

## The problem and the theorem

Fix $`n \ge 2`$. A set $`A = \{a_0 < \dots < a_{n-1}\}`$ of residues in
$`\mathbb{Z}_N`$ is **valid mod $`N`$** if the all-ones multiset is the *only*
size-$`n`$ multiset drawn from $`A`$ whose sum is $`p = \sum a_i \pmod N`$.
Validity is exactly the condition under which the permanent of an
$`n \times n`$ matrix equals a single coefficient of its row-product
polynomial mod $`x^N - 1`$, extractable by a size-$`N`$ transform (a DFT over
$`\mathbb{C}`$, or a number-theoretic transform over a finite field) — so one
wants the smallest modulus $`N`$ that is still valid.

For the super-increasing set $`A = \{2^k - 1 : 0 \le k < n\}`$ the paper proves

> **Theorem.** $`N_{\min}(n) = 2^n - 2^{\lfloor \log_2 n \rfloor}`$ for all $`n \ge 2`$.

The Lean development proves exactly this, for all $`n \ge 2`$ (not up to a
bound): the main theorem `nmin_eq` states
`IsLeast {N | 2 ≤ N ∧ Valid n N} (2^n − 2^m)` with `m = Nat.log 2 n`, combining
the paper's Theorem A (validity / upper bound) and Theorem B (lower bound).
That this $`N`$ is minimal over *all* residue sets (not just the
super-increasing one) remains a conjecture (Conjecture 1 in the paper,
CP-certified for $`n \le 7`$) and is not proved here; the formalized partial
results and remaining critical-range G1/G2/G3 interfaces are summarized below.

## Conjecture 1: current proof frontier (2026-09-09)

For `n >= 16`, any actual affine chain with
`n+2*floor(log_2(n)) <= 2*m` now gives the original global and every
exact-stratum lower bound. `LongChainCycle.lean` allows arbitrary
endpoints and remaining coordinates: maximal continuation yields a
majority cycle after bounding its incoming tail. Genuine endpoints
still give the stronger binary bound at the earlier cutoff
`n+floor(log_2(n))+4 <= 2*m`. The unrestricted conjecture remains open
for arbitrary high-escape tuples whose actual chains are shorter.

Any `r >= 2` disjoint actual affine chains of length `m >= 4` now
give every original global and exact-stratum bound when
`n+r*floor(log_2(n))+r+3 <= (r+1)*m`. `MaximalChainFamily.lean`
retains arbitrary endpoints and remaining coordinates, and arbitrary
arity through extension, suffix splicing and actual majority-cycle
extraction. Unequal families have explicit combined-cover thresholds.
The unrestricted high-escape, short-chain residual remains open.

`FamilyAggregateCycle.lean` now sharpens unequal-family coverage by
charging the incoming prefix and all surviving chains jointly. At any
depth, `B=2^t` and `D=t*B-(B-1)`, the condition
`B*n+2*r*D <= 2*(B-1)*S` gives the original bounds together with the
continuation charge. This reaches families below both the prior
single-chain and separate-logarithm coverage cutoffs.

`ChainFamilyProfile.lean` further replaces the full-factor charge by
the actual truncated error `product min(n,2^L_i)*2^(n-S)`. Controlled
extension and splicing preserve it, so short and empty members retain
their exact contributions. The original bounds follow with the same
collective coverage criterion and arbitrary endpoints.

Every hypothetical global or exact-stratum counterexample now obeys
quantitative escape-count bounds at every shift, including tuples with
actual opposite pairs. `CollisionForest.lean` preserves a widest genuine
arm while cutting the unique collision; `CollisionEscapeThreshold.lean`
pays for that cut with `r+1` in the scalar threshold. The sharper
`CollisionEscapeCeiling.lean` uses the rounded-up average, and the
exactly equivalent G3 gate now retains its unconditional all-shift
restriction, including actual opposite pairs. The earlier stronger
injective bounds remain. Arbitrary escape extraction and all
three unrestricted obligations remain open.

`GlobalFewEscape.lean` now proves the complete global and exact-stratum
bounds for at most two escapes from length 52 and at most three from
length 101, including opposite pairs. Global and G3 counterexamples
must have at least three/four escapes at every shift in these ranges.

The original critical closure gives half descent at any actual
escape count satisfying the explicit binomial threshold. Every critical
no-half parent of length `k >= 4` has, at each shift, an escape count `r`
with `k < r^2*(floor(log_2(k))+1)+3*r`. `G1QuantitativeEscape.lean`
feeds the exactly equivalent residual into the same three-gate assembly.

The preceding fixed-count closure gives half descent with at most
four affine escapes from parent length 101. `ChainForestFourEscape.lean`
consumes both cycles and genuine four-chain forests;
`G1LargeFiveEscape.lean` feeds the equivalent five-escape residual to
the same G1/G2/G3 assembly. The unrestricted conjecture remains open.

The earlier three-chain closure is
`binary_card_bound_of_genuine_three_chain_forest_of_length_ge_52`:
all genuine three-chain forests of length at least 52 satisfy `2^n <= |G|`.
Its original critical consumer proves half descent whenever some affine
shift has at most three escapes, in every stratum. Large no-half tuples
therefore have at least four escapes at every shift. Earlier profile
queues below are historical within this now-closed large forest class;
the unrestricted conjecture and G1/G2/G3 remain open.

Conjecture 1 remains open. `G1PureStarElimination.lean` proves a
dimension-free simplification: a nonempty global pure-edge omission star
under failure of common touch forces a three-omission witness. It does not
assume G2 or criticality. The star arm has been removed from the existing
protected private-heavy endpoint. Its historical leaf-cycle and odd-kernel
continuations are no longer required on that proof path, although their
standalone conditional theorems remain available.

`G1CriticalThreeOmissions.lean` now proves the stronger all-dimensional
frontier: every valid even-modulus tuple with `N < 2^n` has common touch or
a three-omission half-witness. The proof changes the subset-sum anchor and
excludes the complete pure-edge triangle; it assumes no G2.

The conditional theorem `global_lower_bound_of_primitive_threeOmissionDeleteStep`
requires exactly these three still-open inputs:

- `PrimitiveThreeOmissionDeleteStep`: deletion in critical three-omission
  cases whose EVERY deleted subtuple affinely generates the ambient group;
- `OddStratumLowerBound` (G2): the all-dimensional odd threshold;
- `ExceptionalLiftObstruction` (G3): the uniform exceptional-lift exclusion.

There are no separate crossing, private-heavy, odd-kernel, or `n<7` base
inputs on this route. Their old deletion theorems have not been proved;
their separate obligations have been bypassed by the new general frontier.
Conjecture 1 and all three global obligations remain open. Historical local
lemma counts do not measure the fraction of the global proof completed.

`PrimitiveCriticalInduction.lean` proves this strengthened sufficient route
by strong induction on tuple dimension. The child bound used by affine
compression is derived INTERNALLY, not supplied as a fourth assumption.
Proper retained cosets already give half children or smaller-counterexample
contradictions; tuples of length at most three have direct parity children.
The original `CriticalThreeOmissionDeleteStep` implies the new restricted
input, and the old global theorem remains available. This is a proved
restriction of G1, not a claim that either version of G1 has been solved.

`G1ParityFibreDescent.lean` now removes another part of the SAME G1 input:
if all but one entry have the same parity, deleting the exceptional entry,
translating the retained coset, and halving its even representatives gives
the required valid smaller tuple. No SI structure or common touch is needed.
The original three-omission deletion obligation is proved equivalent to
its restriction to tuples with at least TWO entries of each parity. A new
conditional global assembly uses exactly that restricted G1 premise, G2,
and G3. All three remain open; no additional gate or parity classification
is assumed.

`SILiftParityDescent.lean` now proves actual half-modulus descent for every
`n>=5`, `4 | N`, `N<2^n` whose actual half quotient contains a unit-affine
SI prefix of length `n-1`. All independent lift bits and the extra entry
are allowed. A three-term defect forces a dyadic complement; an even
extra then forces coherent interior lifts, while an odd extra supplies
the large parity coset directly. The coherent branch constructs a smaller
valid fixed tuple from power-gap rigidity. This removes this whole class
from higher-even G1, without assuming common touch, criticality, G2, or
G3. It does not cover the first even stratum or arbitrary tuples, and
does not assert a general singleton-parity classification.

`SILiftOddDefects.lean` now narrows the corresponding FIRST-even critical
class: for odd `M`, `N=2*M<2^n-2`, `n>=5`, a full unit-affine SI quotient
prefix forces exactly ONE noncoherent entry among the first `n-2` lifts,
relative to the actual lifted-one difference and lifted zero. Two defects
would force equal even dyadic sums below `2*M`; oddness removes wraparound
and gives a forbidden quotient collision. Zero defects already violate
the coherent class bound. `SILiftOddNormalForm.lean` now also proves the
terminal lift coherent and determines the extra upstairs as
`c*(1+2^j-2^l)`, with `3<=l<=n-2`, `l!=j`, and actual lifted-one multiplier
`c`. General pair-sum rigidity supplies this further extraction. If the
original lifted zero and one share parity, actual coset halving now gives
G1 descent in this first-even class, with quotient affine transport.
`SILiftOddComplete.lean` now excludes the opposite-parity branch as well:
the full first-even threshold `2^n-2<=N` is proved for this entire class,
all original lift bits and extras, `n>=5`. Below the binary bound the
half modulus must be the Mersenne endpoint, giving a smaller fixed valid
tuple. Together with higher-even descent, actual G1 half descent is now
proved for every subbinary full unit-affine SI quotient-prefix lift in
EVERY even stratum. Arbitrary-prefix extraction, shorter independent
prefixes, and unrestricted G1/G2/G3 remain open; no new gate is added.

`SILiftFullBound.lean` now proves the full numerical global bound AND
every exact even-stratum bound for this full unit-affine half-quotient
prefix class, in every dimension `n>=3`. Below `2^n`, validity implies
fixed-set validity at the SAME modulus. Actual odd-coset halving preserves
the required next quotient prefix, closing the structured induction;
the proved uniform lift cover excludes an oversized doubled child gap.
All lift bits and extras remain arbitrary. Only the fixed n=3,4 induction
bases use kernel-checked finite enumeration. Arbitrary-prefix extraction
and unrestricted G1/G2/G3 are still open, 0/3.

`SILiftMultiplier.lean` now removes the unit restriction for every n>=5:
the full global and exact even-stratum bounds hold for ANY quotient
multiplier together with arbitrary independent lift bits. Dividing the
actual prefix by the multiplier's subgroup index leaves only indices
one or two below the binary bound. Index two forces a child power gap
and an actual terminal-prefix quotient collision, consumed by the proved
half-deletion theorem. This closes the nonunit full-prefix residual; it
does not extract prefixes from arbitrary tuples or close a global gate.

A shorter coherent prefix now suffices in a uniform dimension range:
`SIThreeExtensionBound.lean` proves the global and EVERY exact-stratum
bound for a coherent unit-affine SI prefix of length n-3, with three
arbitrary extras, now for all n>=7 and positive moduli. Below 2^n, an actual
extra extends the prefix; one swap invokes the proved two-extra theorem,
giving fixed validity at the SAME modulus and an admissible power gap.
Fifteen bounded-multiplicity rivals yield a symbolic interval contradiction
in all dimensions in this range. The five-outside-coin case uses one
shorter Mersenne prefix. No finite census or global gate is assumed.
Three added rivals lower the requirements to m>=4,L>=2m-1, superseding
the earlier n>=13 cutoff. For N<=2^n-3, the entire ACTUAL SI tuple is
recovered with the same affine map after reindexing, including at the
global endpoint. All nineteen declarations are in the axiom audit; the
full 15,112-job build and all 3,085 standard-only axiom lists pass.
General nonunit three-extra scaling
and arbitrary-prefix extraction are not asserted. This closes a broader
structured class, not an unrestricted gate: G1/G2/G3 remain open, 0/3.

`SIOneExtraFibreCover.lean` now proves a stronger binary bound for one
nonunit three-extra class in G1's two-large-parity-fibre residual. For
every n>=7 and N=2M>0, a doubled coherent SI prefix of length n-3 with
extra parities even/odd/odd implies `2^n<=N`. Reindexing and translation
are allowed; all three extra values are otherwise arbitrary. The actual
n-2 entry large fibre gives a valid one-extra SI tuple modulo M. Below
twice its binary threshold, that tuple covers every residue with n coins.
Mapping the cover back gives a rival omitting both minority coordinates.
The global and every exact-stratum bound follow without any global gate.
Eight declarations, including the uniform cover and translated binary
consumer, are in the axiom audit; the full 15,113-job build and all 3,093
standard-only axiom lists pass.
This does not classify arbitrary two-large-fibre tuples or prove arbitrary
three-extra scaling. The same unrestricted G1/G2/G3 gates remain open.

`SIThreeOddTargetPacking.lean` proves the global and every positive-
stratum bound for the three-opposite-parity pattern, every n>=8, with
translation/reindexing. Its stronger numeric conclusion is `2^n-2<=N`;
for n>=9 the binary bound also follows. Three actual removed-coordinate
targets modulo M=N/2 avoid an initial prefix cover and must be pairwise
farther apart than the prefix sum. Packing their representatives gives
M>=C+2S+3, where m=n-3, C=5*(2^(m-1)-1)-(m-2), S=2^m-m-1. The
packing theorem holds m>=4; the numeric cutoffs are not silently lowered.
Eleven declarations include a general actual-mapped-fibre rival lemma
and the concrete global/even-stratum consumers. The full 15,114-job build
and all 3,104 standard-only axiom lists pass. No finite census or unproved cover is assumed. Arbitrary prefix
extraction and unrestricted G1/G2/G3 remain the same three open gates.

`SIThreeDoubleBound.lean` now closes ALL parity patterns for the index-two
three-extra class, every n>=8. A coherent doubled n-3 prefix, up to an
additive automorphism and translation in the original modulus, implies
the global and every exact even-stratum bound with three ARBITRARY extras.
Subbinary validity implies fixed validity at the SAME modulus. Two even
extras give an actual two-extra child: below its last two binary residues,
whole-child extraction yields an actual longer prefix upstairs; the top
two residues have admissible doubled small gaps. The other patterns use
the preceding cover and packing theorems. Six new declarations include
actual-child construction, all-parity combination, affine transport, and
the final global/stratum consumers. The full 15,115-job build and all
3,110 standard-only axiom lists pass.
No index-two parity case remains open in this range. Other subgroup
indices and arbitrary extraction are not asserted; the same unrestricted
G1/G2/G3 gates remain open, 0/3.

`SIThreeIndexThree.lean` closes ALL index-three three-extra patterns for
every n>=9. A coherent tripled n-3 prefix, with arbitrary extras and
original-modulus unit-affine transport/reindexing, forces `2^n<=N` for
every positive modulus divisible by three, including odd moduli. Global
and all stratum thresholds follow. Validity gives unconditional extra
localization and a tight full-group cover using the actual one-extra
fibre's own coin budget. Actual child validity, prefix-only rivals and
two-target separation complete the mechanisms at arbitrary subgroup
index; elementary ZMod 3 arithmetic then consumes every index-three
pattern. Eleven new declarations include the final binary and all-stratum
consumers. The full 15,116-job build and all 3,121 standard-only axiom
lists pass. No finite tuple census or
unrestricted G1/G2/G3 premise is used. Arbitrary extraction and other
subgroup indices are not claimed; no index-three subcase remains queued.

`SIThreeIndexFour.lean` closes ALL index-four three-extra patterns for
every n>=8. A coherent quadrupled n-3 prefix with arbitrary extras and
original-modulus unit-affine transport/reindexing implies subbinary fixed
validity at the same modulus, hence global and every exact even-stratum
bounds. Three same-coset extras force three actual cyclic gaps of length
at least S+1, where S=2^m-m-1; the wrapping gap is essential. Subgroup
entries give actual next-entry extraction, or admissible gaps four/eight
at the top two child residues. Subgroup-sum rivals consume the other
quotient patterns. Ten declarations include general actual-difference
and cyclic-packing lemmas and the final numerical consumers. The full
15,117-job build and all 3,131 standard-only axiom lists pass. No index-four
subcase remains open in this range;
arbitrary extraction and unrestricted G1/G2/G3 remain open, 0/3.

`SIThreeIndexFive.lean` closes ALL index-five three-extra patterns for
every n>=8, proving the binary bound for arbitrary extras and original-
modulus unit-affine transport/reindexing, including odd moduli. The global
and all stratum thresholds follow. A subgroup extra yields an actual
one-extra child with too large a proved lower bound; an opposite pair
has a prefix-only rival. Equal residues are excluded using the m-coin
cover in both directions: S+w and S-w cannot both lie above S for
M<=2S+1. This works even when the prefix does not cover the whole
subgroup. Elementary quotient arithmetic consumes every pattern. Seven
new declarations include the complete binary and all-stratum consumers.
The full 15,118-job build and all 3,138 standard-only axiom lists pass.
No tuple census or unrestricted global
gate is assumed; no index-five subcase remains open in this range.

`ActualFibreQuotientCube.lean` proves a general counting constraint with
NO SI hypothesis: if an actual m-entry cyclic fibre covers its subgroup
using exactly m coins, then every outside-coordinate subset sum is
distinct in the quotient. Thus k outside entries force index at least
2^k. More generally an (m+r)-coin cover excludes subset collisions whose
cardinalities differ by at least r. Padding uses an actual fibre entry,
which need not be zero. For even fibres this excludes full own-size
covers with at least two outside coordinates, and an (m+2)-coin cover
already excludes two odd extras. These are general G1 restrictions;
full coverage is not proved for arbitrary critical fibres.
The same counting theorem closes ALL index-six/seven coherent three-extra
classes for n>=8, with the binary bound and hence every global/stratum
threshold, including odd moduli at index seven. No quotient enumeration
is used. The full 15,119-job build and all 3,146 standard-only axiom lists
pass. Eight declarations are new. An injective index-eight quotient cube
alone does not ensure validity. Its index-eight equality case is now
closed below; arbitrary extraction and unrestricted G1/G2/G3 stay open, 0/3.

`SIThreeIndexEight.lean` closes ALL index-eight three-extra patterns for
n>=8, with original-modulus affine transport, same-modulus subbinary
fixed validity, and all global/exact even-stratum bounds. The full actual-
fibre cover also excludes tripled outside totals. Elementary arithmetic
modulo eight then orders the quotient extras into a dyadic chain. Actual
two-extra children and one-hole covers force Y=2X+8 and Z=2Y+8; the
parity-saving cover forces X mod M=-7 when M is even. These relations
close the entire actual tuple under v -> 2v+8, including its prefix wrap.
The odd-M endpoint has admissible original gap eight. Twelve declarations
include general arbitrary-index doubling extraction and arbitrary-fibre
repeated-total exclusion. Full 15,120-job build; all 3,158 axiom lists
standard-only. The arbitrary-multiplier assembly is now complete below;
no new global gate is introduced.

`SIThreeMultiplierBound.lean` closes the ENTIRE arbitrary-multiplier
coherent three-extra class for every n>=9. A prefix c*(2^i-1)+b of length
n-3, with ANY multiplier c (including nonunits) and three unrestricted
extras, forces the full global and all exact-stratum lower bounds. Below
2^n it forces fixed validity at the SAME modulus. A uniform endpoint
ratio and actual reflected prefix validity bound the normalized subgroup
index by eight; the completed index results consume all cases. Original-
modulus unit-times-divisor normalization removes the multiplier restriction.
Ten declarations include direct critical-G1, odd-G2, and exceptional-G3
exclusions for this full class. No new census, global premise, or unproved
structure assumption is inserted into the global induction. Full 15,121-
job build; all 3,168 axiom lists standard-only. The index-one-through-eight
queue is closed in this range. Arbitrary prefix extraction, shorter
independent lifts, and unrestricted G1/G2/G3 remain OPEN, 0/3.

`ActualFibreCoverDeficit.lean` returns to ARBITRARY actual fibres and
removes the full-cover assumption. If C is the exact-m-coin sumset of an
actual m-entry fibre, d its subgroup index, and k the number of outside
coordinates, validity forces d*|C|+2^k<=d*(M+1). Equivalently, h missing
residues allow at most d*(h+1) outside subsets. For an even fibre,
|C|+2^(k-1)<=M+1. Minimum-cardinality representatives in quotient buckets
charge every other subset to a DISTINCT genuinely uncovered residue;
actual nonzero padding is explicitly compensated. No SI structure,
criticality, zero-entry, or complete-cover premise is required. Eight
declarations include the exact sumset and the direct arbitrary-even-fibre
consumer. Full 15,122-job build; all 3,176 axiom lists standard-only.
This is a quantitative restriction on the same G1 residual, not a new
open gate or a sufficient validity test. Deriving enough cover growth
from arbitrary criticality, or actual deletion, remains unproved; 0/3.

`ActualFibreSumsetPacking.lean` strengthens this GENERAL fibre restriction.
For any nonempty outside quotient-zero subset of size r, the ACTUAL
coin sumsets satisfy |C_m|+|C_r|<=M. Validity dissociation gives the
arbitrary-budget bound |C_r|>=sum_{j<=r} binom(m-1,j). Thus an even
m-entry fibre with two odd outsiders must miss at least binom(m,2)+1
own-size sums (and at least m by a direct translate argument). These
are genuine disjoint reflected sumsets, with no SI, zero-entry, complete-
cover, or criticality premise. The one-hole saturation case proposed
above is therefore excluded outright for m>=2, not left as a deletion
obligation. Eleven declarations include all budgets and all subgroup
indices. Full 15,123-job build; all 3,187 axiom lists standard-only.
Even exact sumset packing is only necessary: a verified invalid parent
can satisfy equality. Arbitrary critical cover growth or actual deletion
is still missing; no global gate is added or closed, 0/3.

`ActualFibreMixedRivals.lean` now gives a COMPLETE criterion for an
arbitrary actual fibre and two extras: parent validity is equivalent to
fibre validity plus exclusion of every nonstandard outside-multiplicity
residual. With two odd outsiders x,y, write alpha=x mod M and extract
the actual divided difference tau(w)=y-x. The explicit target grid is
T(q,B)=sum(u)+alpha+w-q*alpha-B*w with prefix budget m+2-2q,
for 2q<=m+2, B<=2q, excluding only (q,B)=(1,1). This captures mixed
rivals with both outside entries present, not just omission rivals.
Eight declarations include both directions of the equivalence and actual
difference extraction, with no SI, criticality, or normal-form premise.
Full 15,124-job build; all 3,195 axiom lists standard-only. The packing-
equality counterexample is detected by a mixed grid point; fibre validity
cannot be omitted from the criterion. Proving a covered grid point from
arbitrary criticality remains OPEN; no unrestricted G1/G2/G3 gate is closed.

`ActualFibreSidon.lean` connects general coin counting to ACTUAL descent.
In a valid tuple, a squarefree pair sum has no other two-coin
representation. The only possible unordered-pair collisions are between
two repeated coordinates. In any actual cyclic fibre of an even parent,
such a collision gives an antipodal parent pair and the required valid
tuple with one fewer coordinate at half the modulus. Otherwise the
fibre has exactly binom(m+1,2) two-coin sums. Thus two odd outsiders
give actual half deletion OR at least binom(m+1,2) missing own-size
sums, improving binom(m,2)+1. At odd fibre order the sharp count and
deficit hold outright. All subgroup indices and arbitrary actual fibre
shapes are allowed; no SI, primitive, zero-entry, or criticality premise.
Ten declarations; full 15,125-job build; all 3,205 axiom lists standard-
only; 161 regression tests pass. Exact Sidon counting plus packing still
does not force a critical grid hit. The same three gates remain OPEN.

`QuotientRivalParity.lean` now gives a COMPLETE first-even lift criterion
for an arbitrary quotient, without any prefix hypothesis. Every nonzero
balanced quotient rival c must have parity dot product one with the
actual lift's parity vector. Conversely any vector separating ALL rivals
constructs an actual valid cyclic lift by CRT. An odd family of rivals
with coordinatewise even total rules out every first-even lift. The
general higher-even obstruction retains the carry condition: if the
coefficient sum is 2*d, then sum(d_i*q_i)=0 in the actual quotient.
Odd half-modulus makes this automatic; an explicit valid higher-even
control shows why it cannot simply be dropped. Six declarations; full
15,126-job build; all 3,211 axiom lists standard-only; 177 tests pass.
A parity certificate excludes every lift of an injective Sidon quotient,
so this goes beyond pair counting. The criterion is closed, but extracting
a dependence or a valid deletion from arbitrary criticality is still open.
This is a general tool inside the existing G1/G3 work, not a fourth gate.

`CyclicLiftCarry.lean` now completes the lift equations at EVERY positive
half-modulus, including all higher-even and exceptional G3 moduli. For
any base lift v, each quotient rival has an actual base carry kappa in
ZMod 2; every cyclic lift is v plus actual kernel bits b. Validity is
equivalent to kappa(c)+sum(c_i*b_i)=1 for EVERY quotient rival, and the
all-lifts existence equivalence is proved in both directions. A finite
zero-parity dependence excludes every lift when its carry sum differs
from the family size modulo two, for ODD OR EVEN families. In particular,
two identical-parity rivals with opposite carries suffice. Re-basing
changes carries by the exact parity dot product; nothing depends on a
silently chosen canonical lift. Thirteen declarations; full 15,127-job
build; all 3,224 axiom lists standard-only; 197 tests pass. The valid
higher-even control is preserved, while an opposite-carry pair excludes
all lifts of a quotient at an exceptional modulus. Critical/exceptional
certificate extraction remains unproved; no unrestricted gate is closed.

`CyclicLiftCertificate.lean` now proves finite certificate COMPLETENESS.
An arbitrary binary equation family has either one solution to ALL rows
or a finite subset summing to zero on the left and one on the right.
Linear separation proves this even for an infinite row index type.
Consequently every arbitrary quotient, at every positive half-modulus,
has an actual valid cyclic lift OR a finite inconsistent carry certificate.
Such certificates are necessary and sufficient for excluding all lifts.
The existing G3 gate is EXACTLY equivalent to supplying them for every
exceptional quotient; it is not replaced by an extra global assumption.
Six declarations; full 15,128-job build; all 3,230 axiom lists standard-
only; 213 tests pass. Critical/exceptional certificate extraction remains
unproved, as does unrestricted G2. All three global gates remain OPEN.

`SmallLiftCertificate.lean` sharpens completeness to a dimension-sized
certificate: a nonempty n-coordinate quotient has no valid cyclic lift
iff at most n ACTUAL rivals have zero total parity and inconsistent
carry. A span-support argument first gives n+1 rows for arbitrary binary
systems; balance removes one coordinate and improves this to n. Thus
the SAME unrestricted G3 gate is exactly universal extraction of these
at-most-n certificates at exceptional quotients. Five declarations;
full 15,129-job build; all 3,235 axiom lists standard-only; 231 tests
pass. The bound is sharp for generic balanced binary systems, not
claimed sharp for realizable quotient rivals. Uniform critical or
exceptional extraction remains unproved; all three gates stay OPEN.

`CycleFibreCapacity.lean` now extracts exponential outside capacity
from an ACTUAL affine doubling cycle of m coordinates. The cycle fills
its subgroup of exact order 2^m-1 with exactly m coins. Any k outsiders
therefore force (2^m-1)|N and 2^k*(2^m-1)<=N. At odd N, m>=k gives
the FULL odd threshold: a cycle containing at least HALF the tuple
suffices, with arbitrary other entries. At any positive N, at most
floor(log2 n) outsiders give the FULL global and EVERY exact-stratum
bound and direct G3 exclusion. The subbinary majority-cycle modulus
is exactly 2^n-2^k or 2^n-1. Affine translation and reindexing are
included; no outside prefix, parity, or lift-bit pattern is assumed.
Ten declarations; full 15,130-job build; all 3,245 axiom lists standard-
only; 253 tests pass. A valid majority-cycle control lies outside the
old coherent n-3 prefix class. General cycle/certificate extraction
remains unproved; unrestricted G1/G2/G3 stay OPEN, not 1/3 closed.

`CycleChainRigidity.lean` now EXTRACTS the logarithmic size restriction
when the outsiders form one actual doubling chain. In ANY abelian
group, a disjoint nonempty zero-sum m-fibre and k-chain force 2^k<=m+k:
binary coin splitting otherwise gives a full-length rival omitting the
entire fibre. The zero-sum fibre need not itself be a cycle. For an
actual affine cycle plus one chain, this supplies the size input to
cycle-fibre capacity and proves the FULL global, odd, every exact-
stratum, and G3 class bounds without assumed component-size cutoffs.
Nine declarations; full 15,131-job build; all 3,254 axiom lists standard-
only; 280 tests pass. Actual omitted-fibre rivals and tight valid controls
are tested, including a valid arbitrary-outsider guard showing that
the chain assumption cannot be dropped from size extraction. Arbitrary
cycle/chain extraction and the three unrestricted gates remain OPEN.

`AlmostDoubling.lean` now EXTRACTS the actual cycle-chain geometry
from a permutation following doubling except at one coordinate. The
complement can be empty, when the entire chain reflects to fixed-set
validity at the SAME modulus. Finite completion supplies the permutation
from one-escape affine doubling closure with doubling injective away
from the exception. At ODD modulus validity makes that injectivity
automatic: the FULL odd threshold holds for every one-escape tuple,
without assumed cycle, chain, prefix, or component sizes. At even
moduli the global, every exact-stratum, and direct G3 consumers retain
off-exception injectivity; an antipodal pair through the exception is
allowed. Ten declarations; full 15,132-job build; all 3,264 axiom lists
standard-only; 309 tests pass. Actual completion, affine reindexing,
and the even collision restriction are tested. A valid odd control
requires three escapes for every affine shift, so general closure
extraction is not asserted. Conjecture 1 and G1/G2/G3 remain OPEN, 0/3.

`OneEscapeDescent.lean` now removes even injectivity from ACTUAL
one-escape half descent. An antipodal pair can be deleted while retaining
the exception, and the specified half quotient still has one-escape
closure. Induction proves 2^n-2^s<=2^s*q in every stratum, giving the
FULL global and exact-stratum thresholds whenever s<=floor(log2 n),
including all odd and first-even cases. At EVERY critical even stratum
the class now has the G1 half-deletion conclusion: a collision gives
actual descent, while injective doubling contradicts the proved bound.
Seven declarations; full 15,133-job build; all 3,271 axiom lists
standard-only; 329 tests pass. Valid branched examples have a collision
disjoint from the actual escape, testing the newly covered case.
Above the logarithmic cutoff the uncapped inequality is weaker and
still admits the exceptional modulus; G3 is not silently closed.
Unrestricted G1/G2/G3 and Conjecture 1 remain OPEN, 0/3.

`DoubleDefectGrowth.lean` now extracts uniform cyclic-lift obstructions.
Two cancelling doubling defects construct an actual two-extra-coin
multiset with unchanged total, in ANY abelian group. Among m>=3 binary
involutive defects such a pair always exists. A half-quotient doubling
block therefore cannot coexist with an upstairs zero-sum pair. Two
copies of the quotient involution force that zero sum under validity,
excluding EVERY lift with arbitrary independent bits. Separately,
two actual rivals with nonzero weighted half-difference exclude all
lifts; `(x,2x,4x,h,x)` with nonzero quotient involution h supplies
explicit two-row obstructions anywhere in a larger tuple. Other
coordinates remain arbitrary. Eight declarations; full 15,134-job
build; all 3,279 axiom lists standard-only; 358 tests pass. Genuine
non-SI valid power-gap controls rule out a blanket SI endpoint shortcut.
The uniform obstruction rules are closed; forcing a pattern from
arbitrary criticality remains open. Conjecture 1 and G1/G2/G3 stay 0/3.

`CycleInvolutionLift.lean` now closes EVERY duplicate branch of the
cycle-plus-involution next-lift family. A quotient doubling block of
m>=3 entries, a nonzero quotient involution, and a duplicate of ANY
retained coordinate admit no valid cyclic lift. Repeating the
involution gives opposite actual lifts. Repeating a cycle entry
extracts ACTUAL quotient-block validity, which forces three distinct
successive coordinates and hence the local carry obstruction. Neither
validity nor local geometry is an extra premise. Independent lift
bits and subgroup indices remain arbitrary. Four declarations; full
15,135-job build; all 3,283 axiom lists standard-only; 380 tests pass.
This complete family exclusion does not classify arbitrary one-escape
endpoints or close unrestricted G3; the three global gates remain 0/3.

`TightQuotientCube.lean` now extracts the FULL outside dyadic geometry
at exact cyclic capacity. Character factorization forces an ACTUAL
half coordinate in a bijective even quotient cube. Removing that
coordinate and reducing the actual remainder preserves cube bijectivity.
Iteration constructs a permutation with q(E i).val mod 2^(i+1)=2^i:
one coordinate at every two-adic level. Both half-coset and full-basis
consumers apply to ANY actual full-cover fibre at tight power-of-two
quotient capacity, including non-SI fibres. No quotient ValidTuple
premise is assumed, and cube descent is not mislabeled G1 tuple
descent. Eight declarations; full 15,136-job build; all 3,291 axiom
lists standard-only; 405 tests pass. Tests retain actual indices,
non-SI fibres, and a tight cube which is not a valid tuple. Critical
coverage/tightness is not yet extracted; unrestricted G1/G2/G3 stay 0/3.

`CycleThinCover.lean` now connects quotient relations to ACTUAL
outside equalities. Uniform binary supports plus cyclic predecessor
splitting cover every nonzero Mersenne residue with m-1 coins, and
every residue outside zero and the negative cycle entries with m-2.
Beside any actual mapped Mersenne cycle, an outside double in the
cycle subgroup must be zero or an actual cycle entry. A quotient
doubling relation between two outsiders must hold upstairs exactly;
otherwise three copies of one outsider and a thin cover form an
actual omitted-coordinate rival. The mapping need not be assumed
injective. Seven declarations; full 15,137-job build; all 3,298 axiom
lists standard-only; 441 tests pass. Next extract quotient doubling
closure from tight actual-fibre capacity. Arbitrary critical structure
and the same unrestricted G1/G2/G3 gates remain open, 0/3.

`TightFibreDoubling.lean` now completes the outside quotient geometry:
ANY actual full-cover fibre at index 2^k forces its k outsiders to
form ONE complete quotient doubling chain under an actual permutation.
Subset-sum injectivity makes a subset representing 2*q_i disjoint
from i; a full-cover actual rival excludes two or more removed entries.
Thus quotient doubling is closed up to zero. The actual half entry
and almost-doubling decomposition then give a chain: every nonempty
cycle remainder would be a zero-sum subset, contradicting the cube.
No SI, cycle fibre, quotient-validity, or outside-size premise is used.
Seven declarations; full 15,138-job build; all 3,305 axiom lists
standard-only; 467 tests pass. A valid non-SI control has quotient
doubling but NOT upstairs doubling, so the distinction is explicit.
Next combine cycle thin covers with this chain to extract the missing
size cutoff for tight cycle fibres. Arbitrary critical extraction and
the same unrestricted global gates remain open, 0/3.

`CycleTightRigidity.lean` now closes the FULL majority-cycle class:
an actual affine doubling cycle of m>=2 entries with k<=m arbitrary
outsiders satisfies the global and EVERY exact-stratum bound, plus
direct G3 exclusion. The logarithmic outside restriction is REMOVED.
In the tight-capacity case, arbitrary subgroup embeddings normalize
through an actual bijective scale factor. The extracted quotient
chain lifts upstairs by thin covers; actual chain rigidity forces
2^k<=m+k. Existing subbinary capacity classification leaves only this
case or the harmless Mersenne endpoint, completing the class.
Nine declarations; full 15,139-job build; all 3,314 axiom lists
standard-only; 489 tests pass. Genuine valid above-tight controls
have many unstructured outsiders, so the size cutoff is asserted
only where proved. Next address near-tight quotient holes and
extract usable structure from arbitrary criticality; the same
unrestricted global gates remain OPEN, 0/3, with no new gate added.

`OneHoleFibreChain.lean` now extracts a full outside quotient chain
at index 2^k+1 for ANY actual full-cover fibre. There is one missing
cube value, so odd doubling permits at most one escape; the actual
full-cover rival rule handles represented doubles. Arbitrary subgroup
embeddings and all outside lifts are allowed. For cycle fibres, thin
covers lift the chain and force 2^k<=m+k at this one-hole capacity.
If k=m+1, subbinary capacity permits three indices: tight and one-hole
are impossible, leaving N=2^(m+k)-2. Combined with majority-cycle
rigidity, the FULL global/all-stratum/G3 class now includes every
affine doubling cycle of at least floor(n/2) entries (m>=2, k<=m+1).
Ten declarations; full 15,140-job build; all 3,324 axiom lists
standard-only; 523 tests pass. Nonchain one-hole cubes and genuine
valid non-SI full-cover and almost-half endpoint controls guard scope.
The quotient chain is necessary, not sufficient for parent validity.
General near-capacity/critical extraction remains inside the same
three unrestricted open gates, 0/3; no new global premise is added.

`TwoHoleFibreChain.lean` now handles two missing quotient values.
Character factorization (generalized to any commutative semiring)
shows that the holes have opposite parity and an actual odd entry
exists. With odd half index, one actual odd deletion removes a half
entry or the unique antipodal collision. Retained doubles are nonzero
and injective, so the single even hole allows one escape and forces
a full retained quotient chain. This extraction applies to ANY actual
full-cover fibre, with arbitrary embeddings and lifts. For cycle
fibres, actual subtuple restriction and thin-cover lifting give
2^(k-1)<=m+k-1. Thus the almost-half class k=m+1, m>=3 satisfies the
STRONGER binary bound N>=2^n: its apparent first-even endpoint is
excluded, while the genuine m=2 endpoint is retained. Nine new
declarations; full 15,141-job build; all 3,333 axiom lists standard-only;
544 tests pass. Cube deletion is not claimed as G1 half-modulus tuple
descent. General critical structure and the same three unrestricted
gates remain OPEN, 0/3; tight, one-hole, and two-hole extraction are closed.

`PartialDoublingChains.lean` replaces a prescribed small hole count by
a uniform arbitrary-hole inequality. Partial doubling injections extend
to actual permutations; subset-sum injectivity forces every orbit to
reach an exception. Actual cycle thin covers bound every first-hit path
by `L=floor(log2(2*m))`, giving `k <= |B|*L`. At ANY odd subgroup index d,
the actual full-cover rival rule charges exceptions to missing values
of the original quotient cube. Thus `k <= (d-2^k)*L` for every actual
affine cycle of size m>=2, with k arbitrary outsiders. No majority or
fixed-hole-count premise is used. A direct binary-bound consumer excludes
all subbinary odd indices whenever `(D_odd-2^k)*L < k`, where D_odd is
the largest odd integer at most `(2^(m+k)-1)/(2^m-1)` rounded down.
Arithmetic applicability includes (m,k)=(11,13),(41,44),(105,109), beyond
the half-sized class; these checks are not proof premises. Ten new
declarations; full 15,142-job build; all 3,343 axiom lists standard-only;
572 tests pass. Odd index and strict inequality are essential. Next:
extend the budget to even indices and extract arbitrary critical
structure. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.

`AllIndexHoleBudget.lean` now extends the uniform budget to EVERY positive
subgroup index, including arbitrary higher-even strata. One actual outside
deletion makes retained doubling nonzero and injective. Its exceptions
are charged to the ORIGINAL cube holes plus the deleted target, giving
`K-1 <= (d-2^K+1)*floor(log2(2*m))`. The deleted-target term is essential,
even for a genuine valid parent. Actual same-modulus cycle subtuples
carry the path bound; no quotient validity or G1 half deletion is assumed.
A direct consumer gives `N>=2^(m+K)` when
`(floor((2^(m+K)-1)/(2^m-1))-2^K+1)*floor(log2(2*m)) < K-1`.
It excludes ALL subbinary indices simultaneously; arithmetic examples
(m,K)=(25,27),(53,56),(117,121) extend below half-sized cycles. Seven new
declarations; full 15,143-job build; all 3,350 axiom lists standard-only;
610 tests pass. General index propagation is complete. Next return to
unrestricted critical-tuple extraction; the cycle premise has NOT been
extracted from arbitrary validity. Conjecture 1 and G1/G2/G3 remain OPEN,
0/3 global gates closed.

`AggregateDoublingGrowth.lean` now charges ALL outside doubling chains
to one replacement budget. Beside any nonempty zero-sum m-fibre in any
abelian group, distinct actual doubling targets can be split together;
their number is strictly less than m. More generally a ranked doubling
forest realizes every coin count through its full binary weight, so
`sum_i 2^(rank i) < m+K`. No cycle or full-cover premise is needed for
these actual-group results. Two individually permitted short chains
can jointly violate this stronger constraint. Beside mapped cycles,
thin covers lift quotient forest edges at every positive index, and
inverse-permutation first-hit ranks EXTRACT the forest from the existing
partial permutation and injective cube. Seven new declarations; full
15,144-job build; all 3,357 axiom lists standard-only; 642 tests pass.
Tests preserve genuine valid endpoints and exhibit actual aggregate
rivals for every tested independent lift. The zero-sum premise is
essential. Next use depth-layer occupancy to strengthen the uniform
hole count; arbitrary critical extraction remains open in the SAME
G1/G2/G3 gates. Conjecture 1 remains OPEN, 0/3.

`RankLayerBudget.lean` now bounds EVERY depth layer by the actual
exception count B. Collective growth then gives, for every t,
`2^t*K < m+K+B*(t*2^t-(2^t-1))`, without the prior logarithmic loss.
Odd and all-index actual-cycle consumers, affine normalization, and
direct binary-bound tests are complete. At t=2 the odd test already
handles (m,K)=(5,7),(13,16),(32,36); the all-index test handles
(11,13),(20,23),(38,42), all missed by the earlier log test.
More importantly, a single uniform theorem proves `N>=2^(m+K)` for
EVERY actual affine cycle with K=m+c outsiders, c>=2, m>=3*2^c,
at arbitrary positive moduli and with all original lifts. This is an
unbounded below-half-sized cycle family, not a fixed-deficit census.
Thirteen new declarations; full 15,145-job build; all 3,370 axiom lists
standard-only; 679 tests pass. Next exploit the parity of missing
values at even indices and continue unrestricted critical extraction.
The cycle premise is still not automatic; Conjecture 1 and the SAME
three global gates remain OPEN, 0/3.

`EvenHoleParityBudget.lean` now resolves original cube holes by parity
at EVERY dense even index 2D. Character factorization and density
extract an odd coordinate and exactly D-2^(K-1) even holes. Only these
can terminate doubled coordinates. One actual deletion adds at most
one endpoint; at odd D an odd deletion makes the extra cost ZERO.
Mapped and arbitrary affine-cycle consumers, automatic dense-index
extraction from even subbinary validity, and direct binary bounds are
proved. In particular K=m+c, c>=2, m>=3*2^(c-1) implies N>=2^(m+K)
at EVERY even modulus, halving the previous sufficient cycle-size scale.
No fixed hole count, stratum cap, or lift pattern is assumed. Seven new
declarations; full 15,146-job build; all 3,377 axiom lists standard-only;
708 tests pass. Strict density and the higher-even extra endpoint have
exact controls. Next broaden actual quotient relation lifting beyond
doubling forests and continue critical extraction. Conjecture 1 and
the SAME unrestricted G1/G2/G3 gates remain OPEN, 0/3.

`ThinExpansionLifting.lean` now goes beyond doubling forests. Every
positive r-coin outside expansion gives a forbidden (m-r)-coin target
in an ARBITRARY actual m-fibre; the omitted coordinate is inside the
fibre, with no outside-omission or full-cover premise. If its (m-1)-coin
cover contains every value except possibly its own total, ALL one-coin
quotient expansions lift to exact original-group equalities. This does
not require a cycle or a zero-sum fibre. Actual mapped cycles supply
the thin cover, and any m successive squarefree-target quotient rewrites
would omit the entire cycle. Target sizes, replacement multiplicities,
and sequential target reuse are unrestricted. Ten declarations; full
15,147-job build; all 3,387 axiom lists standard-only; 734 tests pass.
Controls include noncycle/nonzero-sum thin fibres and multi-target
patterns with NO doubling edges. Next extract useful targets or rewrite
patterns from arbitrary critical tuples; their existence is not assumed
proved. Conjecture 1 and the SAME global G1/G2/G3 remain OPEN, 0/3.

`FullCoverExpansionExtraction.lean` now starts extraction itself. A full
actual fibre cover forces EVERY squarefree outside quotient sum to be
uniquely shortest among arbitrary multisets. Failure of validity after
adjoining zero therefore constructs a one-coin expansion. A thin cover
lifts it exactly. For mapped cycles with m>=2 and K>=2, subbinary
validity automatically gives d<globalBound(K+1), so a strictly smaller-
dimensional induction hypothesis extracts an actual first expansion
with a coordinate used at least THREE times. The induction hypothesis
is explicit, not a claim that the global bound has been proved.
Ten declarations; full 15,148-job build; all 3,397 axiom lists standard-
only; 762 tests pass. The valid parent (10,20,5,16,2) modulo 30 has an
extracted first expansion but NO second step: first-step existence is
not enough to omit a two-cycle. Next use genuine counterexample
criticality to obtain compatible further growth or actual descent,
and extract useful fibres from arbitrary tuples. Same three OPEN
global G1/G2/G3 gates, 0/3; no additional conjectural gate is introduced.

`InductiveOutsideSpan.lean` extracts genuine quotient structure. Short-
sum rigidity plus a constant nonzero character constructs a valid tuple
consisting of zero and all outsiders. Beside a subbinary mapped cycle
(m>=2, K>=2), its dimension is strictly smaller and its modulus is
strictly below globalBound(K+1). This ACTUAL smaller-counterexample
construction assumes no global bound. Alternatively, one-coin growth
makes the affine difference span equal the linear span; strict cube
density makes the latter the entire quotient. Under the explicit lower-
dimensional induction hypothesis, outside differences therefore span
the whole quotient from every anchor. Seven declarations; full 15,149-
job build; all 3,404 axiom lists standard-only; 797 tests pass. The dense,
short-sum-rigid tuple (1,7,11,16) modulo 30 has a one-coin expansion and
full affine span, but NO unit pair difference. Affine generation is not
a unit-pair normalization or a repeated-expansion certificate. Next use
this extracted structure and genuine criticality for compatible growth
or actual deletion; arbitrary useful-fibre extraction and G1/G2/G3
remain OPEN, 0/3.

`DeletedOutsideSpan.lean` now constructs an ACTUAL half-modulus child
from any proper one-outsider-deleted quotient span beside an arbitrary
full-cover fibre, provided d<3*2^(K-1). The injective deleted cube forces
the subgroup index to equal TWO; pulling it back and restricting the
original coordinates gives the child, with no induction hypothesis.
For every subbinary mapped cycle with m>=2 and K>=1, both coverage and
the density window are automatic. Thus either the actual half child
exists or EVERY deleted outside span is the whole quotient. At odd
quotient order, full deleted span follows directly from cube density.
Eight declarations; full 15,150-job build, all 3,412 standard-only axiom
lists, and 831 tests pass. This is a
structural extraction of a familiar same-parity deletion branch, not a
solution of the two-large-parity-fibre G1 residual. General useful-fibre
extraction and compatible further growth remain open; G1/G2/G3 stay
OPEN, 0/3. No new global gate is introduced.

`CriticalAffineCompression.lean` now reaches ARBITRARY tuples, with
no cycle, SI prefix, full-cover fibre, or unit-pair assumption. In the
strict three-times-child-bound window, a proper affine coset containing
all but one coordinate constructs either an ACTUAL half-modulus child
or an ACTUAL strict smaller-dimensional global counterexample. The
construction assumes no induction hypothesis. The window is automatic
for every global counterexample of length >=3 and every subbinary tuple
of length >=4. Under the explicit child bound, half descent therefore
holds unless every deleted subtuple affinely generates the whole cyclic
group, from every retained anchor. At odd modulus only full generation
remains. The exact-stratum consumer covers the entire critical G1 range.
Eight declarations; full 15,151-job build, all 3,420 standard-only axiom
lists, and 870 tests pass. The strict
factor-three boundary is guarded by actual valid tuples. Even full
deleted affine generation plus validity does NOT imply a unit pair.
Its standalone theorem keeps the child bound explicit; the next module
now discharges that bound inside the global assembly. No unrestricted
G1/G2/G3 gate closes, 0/3.

`PrimitiveCriticalInduction.lean` closes that integration step. Strong
dimension induction derives the child global bound from previously
proved child strata, uses affine compression and common touch, and asks
G1 ONLY for the primitive three-omission residual. The same exceptional
arithmetic consumes G3; the odd base consumes G2. Both the full stratum
theorem and `global_lower_bound_of_primitive_threeOmissionDeleteStep`
have exactly these THREE explicit inputs and NO child-bound premise.
Seven audited declarations (six theorems and the restricted G1 definition);
full 15,152-job build; all 3,427 axiom lists standard-only; 913 tests pass.
Small actual half children, all power/non-power arithmetic branches, and
the essential exact G3 boundary are checked. Next prove primitive G1
deletion or force an actual contradiction there, alongside the same G2
and G3 obligations. No new structural-extraction gate is introduced.

`OneEscapeCycleLift.lean` now recovers ACTUAL cycles from half-quotient
data. If an injective quotient affine cycle's selected original
predecessors have actual doubling targets, choosing those targets
recovers a cycle among the original coordinates. The selected lift
may change; doubling kills the two-element kernel and makes the cycle
law exact. Parent validity is not needed for the extraction. One-escape
closure supplies the local targets automatically away from its exception.
Consequently actual Mersenne capacity, the full global bound for a
half-sized cycle, and its G3 exclusion now consume quotient cycle data,
not an assumed original cycle or assumed quotient validity. Six theorems;
full 15,153-job build; all 3,433 axiom lists standard-only; 941 tests pass.
Guards show that a bare quotient cycle, an index-three kernel, or repeated
quotient coordinates cannot justify this construction. General quotient-
cycle extraction and the exceptional-on-cycle case remain missing; the
unrestricted G1/G2/G3 gates stay OPEN, 0/3.

`DyadicCycleLift.lean` removes the single-half-step restriction. A
quotient cycle avoiding the exceptional IMAGE stays among actual
coordinates during doubling; after r steps a kernel killed by 2^r
vanishes from the cycle relation. The resulting original cycle is
constructed uniformly in ANY abelian groups, including noncyclic
two-primary kernels. Affine translation and every cyclic quotient
of index 2^r are included. No validity or induction hypothesis is
needed for extraction. Valid parents inherit actual Mersenne capacity
and, for k<=m+1, the full global bound. Six theorems; full 15,154-job
build; all 3,439 axiom lists standard-only; 974 tests pass. The genuine
valid (1,2,4,8) modulo 28 shows that avoiding the exception INDEX
does not suffice at depth two: its quotient image can still lie on
the cycle and stop the actual walk. Next attack the exceptional-image
and quotient-cycle-extraction cases, not a fixed-depth lifting queue.
The same primitive G1, G2, and G3 remain OPEN, 0/3.

`OneEscapeCycleSize.lean` now EXTRACTS the size cutoff needed by those
consumers. In any group with at most one nonzero involution, validity
permits only one unordered equal-double pair, without assuming closure.
Protect an actual cycle and discard one OUTSIDE collision coordinate.
All outsiders except this deletion and the escape then have distinct
outside doubling targets. Simultaneous splitting beside the zero-sum
cycle forces k-2<m, hence k<=m+1. No criticality or valuation premise
is used. EVERY nontrivial actual affine cycle in a cyclic one-escape
tuple therefore gives the full global and all exact-stratum bounds,
and direct G3 exclusion. Arbitrary-depth quotient-cycle consumers no
longer assume a half-size cutoff either; exceptional-image avoidance
is still necessary. A singleton cycle forces the whole length <=3.
Eight theorems; full 15,155-job build; all 3,447 axiom lists standard-
only; 1,019 tests pass. A valid five-tuple modulo 30 makes the +1 sharp;
valid two-escape and noncyclic-two-torsion examples guard both hypotheses.
Deep exceptional families whose cycles FAIL the old size premise now
have explicit simultaneous-splitting rivals. The remaining one-escape
exceptional target in dimensions >=4 is acyclic merging-chain geometry,
not useful-cycle size or lifting depth. Its classification and rival
extraction are not yet proved. Arbitrary primitive G1, G2, and G3 remain
OPEN, 0/3; no additional global gate is introduced.

`FullDepthFork.lean` now closes the FULL-DYADIC-DEPTH fork endpoint.
Suppose an actual A-chain seeded by x merges into an actual L-chain
seeded by y at position B, with A<=B<L and 2^A*x=2^B*y. At
N=(2^L-1)*2^A and A+L<2^A, the tuple is invalid. Validity extracts
exact order 2^A for z=x-2^(B-A)*y from the distinct predecessors.
Cyclicity extracts t<2^A with t*z=(2^L-1)*y, for ARBITRARY seeds.
If t>0, the nonstandard weights X=t-1 and Y=2^(B-A)*(2^A-t)
lie in their two binary ranges and have X+Y>=A+L. Binary refinement
therefore supplies an actual full-length rival. If t=0, the L-chain
is a zero-sum fibre and the A-chain alone supplies that rival. Affine
reindexing and a DIRECT G3 consumer at A=floor(log2(A+L))+1 are proved.
There is no unit, exact-order, calibration, or finite-census premise in
the final fork theorem. Ten theorems; full 15,156-job build; all 3,457
axiom lists standard-only; 1,087 tests pass. The strict budget is guarded
by a genuine valid n=8/N=248 endpoint. Its initially remaining shallower-
arm arithmetic is now closed by the next module; actual fork extraction
from arbitrary one-escape tuples remains unproved. The same primitive
G1, G2, and G3 remain OPEN, 0/3.

`ShallowForkWeights.lean` now closes G3 for EVERY actual two-chain
merging fork, with no arm-depth restriction. In the shallower case,
failure of the first calibrated weight pair forces at least three
common-tail coordinates. This pays for four top coins in the second
pair; the alternative case saves one coin below the all-ones endpoint.
Both actual sum identities and ALL coin budgets are proved uniformly.
An even calibration coefficient would put the entire tuple in the even
subgroup, whose subset-cube lower bound contradicts subbinary size.
Thus oddness is extracted from actual validity, with NO unit assumption.
The final theorem `not_validTuple_exceptional_of_actual_fork` combines
arms of length one/two via existing prefix bounds, the full-depth rival,
the shallower rival, and extracted exact order to rule out overdeep arms.
It takes ONLY actual two-chain data, their merge, and the exceptional
non-power dimension. No order, calibration, depth, coin-pattern, or
finite-census premise remains. Eighteen theorems; full 15,157-job build;
all 3,475 axiom lists standard-only; 1,157 tests pass. Nonunit seeds,
both complementary branches, actual even-coset rivals, overdeep and
lower-order duplicate predecessors, and affine transport are guarded.
The former inverse-weight diagnostic has become a uniform proof for
the shallower arithmetic; it was never used as a proof premise. The
then-remaining one-escape G3 task was structural extraction. It is now
closed by `OneEscapeGeometry.lean`, as detailed below.
Arbitrary primitive G1, G2, G3 remain OPEN, 0/3; no new global gate.

`OneEscapeGeometry.lean` now proves G3 for **ALL one-escape affine-doubling
tuples**. Every finite map either has a first-hit rank to its escape or
an actual nonempty cycle avoiding it. In the ranked case a longest chain
has an injective complement and a unique boundary predecessor, because
validity in cyclic groups permits only one equal-double pair. The
complement is extracted as a second chain; maximality also extracts
`A <= B < L`. Thus the actual parent yields a cycle, full chain, or merging
fork, and all three are excluded by the proved consumers. The n=3 base
uses the general equality-order theorem, not a tuple census. No acyclicity,
rank, permutation, chain/fork, unit, or depth premise remains. Twelve
theorems; full 15,158-job build; all 3,487 axiom lists standard-only;
1,192 tests pass. Finite-graph controls check every labelled absorbing-root
map through seven coordinates with at most one off-root collision, plus
long arms, reversed labels, arbitrary affine shifts and hypothesis guards.
That class-specific G3 is now integrated with its actual closure-preserving
half deletions by `OneEscapeGlobalBound.lean`, as detailed below.
One-escape closure is NOT extracted for arbitrary tuples: unrestricted
G1/G2/G3 and Conjecture 1 remain OPEN, 0/3.

`OneEscapeGlobalBound.lean` proves the FULL global and EVERY exact-stratum
bound for ALL one-escape affine-doubling tuples at every positive cyclic
modulus. Induction uses the actual half-deleted tuple, retaining both its
exception and affine closure. Above the logarithmic cutoff, the child
bound lifts numerically unless the parent is the non-power exceptional
endpoint, excluded by the completed class-specific G3 theorem. No
unrestricted G1/G2/G3 input, doubling injectivity, rank, geometry, unit or
depth hypothesis remains. Seven theorems; full 15,159-job build; all 3,494
axiom lists standard-only; 1,254 tests pass. Actual high-stratum branched
parents/children, affine transport, sharp fixed endpoints, power/non-power
arithmetic and the indispensable exceptional-boundary guard are checked.
The resulting general residual restriction is proved too: any hypothetical
global or exact-stratum counterexample must have at least TWO escaping
doubles at EVERY affine offset. This is not an additional global gate or
a proof that the residual is empty. Next target structural extraction or
actual descent for this genuinely multi-escape residual. The one-escape
branch is now CLOSED, including all valuations; unrestricted G1/G2/G3 and
Conjecture 1 remain OPEN, 0/3.

`FewEscapeCycleBudget.lean` now moves beyond the closed one-escape branch.
For an actual m-cycle and k outsiders with q affine escapes, it EXTRACTS
`k <= m+q` and, at every depth t,
`2^t*k < m+k+(q+1)*(t*2^t-(2^t-1))`. Protecting the cycle costs at most
one collision deletion; all remaining actual nonescaping arrows extend
to a permutation. The outside subset cube forces every orbit to hit an
exception. Collective growth and bounded depth-layer occupancy give the
inequality, without quotient-hole or outsider-size inputs. If
`5*(q+1) <= 2*m+6`, depth two extracts the half-sized cutoff and gives the
FULL global and every exact-stratum bound.
For q<=2, EVERY actual nonempty cycle is now excluded at G3, with NO cycle-
size restriction. Outside the half-sized cutoff, the derived cases are
only (m,k)=(2,4),(3,5),(4,6): exact Mersenne divisibility excludes the first
and last exceptional moduli, and the middle dimension is a power of two.
Singleton cycles and n=3 are consumed too. Twelve theorems; full 15,160-job
build; all 3,506 axiom lists standard-only; 1,294 tests pass. This is a
uniform escape-count argument, not finite tuple enumeration. The valid
subbinary tuple (0,1,4,16,24) modulo 30 has minimum escape count two at all
offsets and is guarded: deleting its lone odd entry leaves an index-two
coset, so it is not in the primitive residual. Unrestricted one-escape
extraction from all subbinary tuples would be FALSE. Bounded searches of
the primitive residual did not settle it; CP runs returned UNKNOWN.
Next address actual acyclic multi-escape data and unrestricted critical
extraction. The entire one-escape branch and all two-escape cycle G3 cases
are CLOSED. The SAME unrestricted G1/G2/G3 remain OPEN, 0/3.

`TwoChainRelations.lean` extracts general restrictions for ACTUAL two
chains of lengths A,L and arbitrary seeds x,y in any abelian group.
Writing K=2^A and H=2^L, validity forbids EVERY positive interior relation
`d*x=u*y` with d<K and u<H. Both opposite weight shifts fit the full
coin budget, and at least one has enough weight for refinement. Hence
fibres of the K-by-H binary weight rectangle are coordinatewise ordered.
An interior zero relation `d*x+u*y=0` forces corner deficits a=K-d,b=H-u
to satisfy `a+b<=A+L+1`, with at least ONE of a,b a power of two.
The proofs assume no merge, unit, cyclic normalization or arm-size
cutoff, and retain arbitrary affine/reindexed chain data. Nine theorems;
full 15,161-job build; all 3,515 axiom lists standard-only; 1,335 regression
tests pass. Strict endpoints and the distinction between one
power deficit and both are guarded by genuinely valid examples.
These are necessary restrictions, NOT full two-chain G3 or an extraction
of acyclic multi-escape geometry. The existence/packing step has now been
completed below; the surviving cyclic deficit arithmetic remains. The SAME three
global gates remain OPEN, 0/3; the completed one-escape branch stays closed.

`TwoChainPacking.lean` now EXTRACTS a nonzero nonnegative rectangle
relation from subbinary group cardinality itself; no collision witness
is assumed. For n=A+L>=5 it is UNIQUE, since two ordered large relations
and their nonzero difference cannot fit in one rectangle. Removing its
translated upper corner leaves an ACTUAL injection into the group.
Consequently there are positive a<=2^A,b<=2^L with
`a+b<=n+1`, `2^n<=card(G)+a*b`, at least one dyadic side, and the actual
relation `(2^A-a)*x+(2^L-b)*y=0`. Axis relations are included.
In particular every actual affine/reindexed two-chain tuple in ANY finite
abelian group satisfies `4*2^n<=4*card(G)+(n+1)^2`. This is a uniform
near-binary lower bound, with quadratic rather than exponential deficit.
Ten theorems; full 15,162-job build; all 3,525 axiom lists standard-only;
1,369 tests pass. These necessary
conditions still do NOT close the sharp cyclic G3 bound: the INVALID
n=10/N=1008 two-chain seeds x=1,y=760 with lengths 4,6 satisfy all corner
conditions with (a,b)=(8,3). Its actual rival is regression-checked.
Next use cyclic arithmetic/full-length rivals to exclude surviving
corners, and extract actual acyclic multi-escape geometry. Do NOT reopen
corner existence/uniqueness/packing. SAME three OPEN global gates, 0/3.

`TwoChainBoundary.lean` now closes a surviving relation class completely.
If `2^A*x=c*y`, `0<c<2^L`, and
`A+L<=(2^(A+1)-1)+(2^L-1-c)`, validity forces c to be a POWER OF TWO:
a non-power complement pays for two extra top coins and an actual rival.
The dyadic coefficient then EXTRACTS a one-escape map. Full global and
EVERY exact-stratum bounds follow, with all affine/reindexed data and
arbitrary nonunit seeds retained. Capacity is automatic when A+L<=2^A.
Any such boundary relation in a remaining global counterexample must
therefore have strictly insufficient capacity and 2^A<A+L; this residual
restriction is proved. The preceding invalid (1,760) G3 corner control
is consumed by its actual 2^4*x=4*y connection.
Nine theorems; full 15,163-job build; 3,534 standard-only axiom lists;
1,408 tests pass. Capacity cannot be dropped: the genuinely valid n=11/
N=20000 tuple with A=1,L=10,x=10510,y=1 has c=1020, a non-power, and
only six units of complementary weight. Next force a usable boundary
relation from surviving cyclic corners or construct a rival directly;
common outside endpoints and unrestricted acyclic extraction remain.
The SAME three global gates stay OPEN, 0/3. No new global gate.

`TwoChainJoin.lean` now closes ALL G3 cases for two actual chains whose
doubled endpoints agree, including a common value OUTSIDE the tuple.
Distinct terminal predecessors extract the full dyadic discrepancy order.
At shallow depth the first calibrated weight pair ALWAYS has enough
weight: failure would require three coordinates after the endpoint
itself. The full-depth calibration also works without an internal merge.
Short arms, overdeep arms, both orientations and arbitrary affine/
reindexed nonunit seeds are consumed. No arm-order, depth, calibration,
oddness or capacity assumption remains in the final class G3 theorem.
Eight theorems; full 15,164-job build; all 3,542 axiom lists standard-only;
1,459 tests pass. The n=7/N=120
tuple (17,34,68,1,2,4,8) guards the genuinely outside common target 16
and two actual escapes; a valid n=4/N=12 control guards non-power
dimension. Next use the ACTUAL identified-endpoint half deletion to
lift this class to the full global/every-stratum bounds, then return
to distinct escaping endpoint images and unrestricted acyclic extraction.
Do not reopen common-endpoint G3 arithmetic. SAME three OPEN gates, 0/3.

`TwoChainJoinBound.lean` completes the common-endpoint branch: FULL
global and EVERY exact-stratum bounds now hold, not only G3. An actual
half deletion identifies the two terminal exceptions, retaining one
exception and all its affine targets. The child lies in the completed
one-escape class. Its exact low-stratum bounds lift directly; the new
common-endpoint G3 excludes the sole high-stratum equality. No induction
or unrestricted conjectural premise is left to supply. All depths,
orientations, affine offsets, permutations and nonunit seeds are allowed.
The generic two-exception deletion also applies beyond chain geometry.
Nine theorems; full 15,165-job build; all 3,551 axiom lists standard-only;
1,516 tests pass. Controls include
genuinely valid large-modulus parents at many valuations and their ACTUAL
half children; the valid n=5/N=30 cycle-plus-outsiders example exercises
the generic affine two-exception deletion. Satisfying the numerical
bound and endpoint relation alone is not asserted to imply validity.
The common-endpoint global/every-stratum branch is now CLOSED. The
unrestricted primitive G1 extraction remains the priority; distinct
escaping endpoint images and general multi-escape geometry are not
classified. SAME three OPEN global gates, 0/3; no extra gate.

`G1TwoEscapeCycle.lean` gives DIRECT G1 half descent for ALL critical
tuples with at most two affine escapes and an actual nonempty cycle.
No common touch forces injectivity of doubling on the whole tuple.
This removes the collision loss: in ANY abelian group, actual m-cycle
data with k outsiders and escape set A satisfy `k<m+|A|` when doubling
is injective. Two escapes and total size at least four extract `m>=2`
and `k<=m+1`, so the exact-stratum cycle bound contradicts criticality.
Otherwise common touch constructs the actual half child. No G2, G3,
primitivity, supplied geometric cutoff or child-bound premise is used.
The final theorem extracts injectivity AND acyclicity for any remaining
two-escape G1 counterexample. Nine declarations; full 15,166-job build;
all 3,560 axiom lists standard-only; 1,563 tests pass. The valid tuple
`(2000,4000,1,3001,2,100)` modulo 6000 guards injectivity: two escapes
and a two-cycle allow four outsiders when doubling collides. Its actual
half deletion is retained. Next extract the actual two-chain geometry
of the injective acyclic residual and consume the corner/packing bounds.
General multi-escape extraction remains open. SAME three OPEN gates, 0/3.

`TwoEscapeGeometry.lean` now EXTRACTS the actual two-chain geometry of
the remaining critical two-escape G1 residual. A generic finite map
either has first-hit ranks to an arbitrary terminal set or has an actual
cycle avoiding it. Two terminal basins are complete disjoint chains when
nonterminal arrows are injective. The original critical tuple without
a half child supplies these hypotheses, and its two allowed exceptions
are proved genuine escaping endpoints. Both original chains, the affine
offset and all coordinates are retained. Rank, acyclicity, injectivity
and decomposition are no longer assumptions. The completed corner and
packing results now give the ORIGINAL tuple a small dyadic-sided corner
paying for its binary deficit and `4*2^k<=4*N+(k+1)^2`, k>=5. Thus
`4*N+(k+1)^2<4*2^k` implies actual G1 half descent. No G2/G3, child
bound or unit normalization is supplied. Nine declarations; full
15,167-job build; all 3,569 axiom lists standard-only; 1,605 tests pass.
Small labelled maps, growing terminal basins, valid affine/nonunit
families, and essential cycle/collision/actual-escape guards pass.
Two-escape geometry and its large-deficit region are DONE. Next consume
the extracted corner's cyclic arithmetic in the quadratic-width band;
this bound is not the sharp conjecture. Unrestricted multi-escape
extraction and the SAME three global gates remain OPEN, 0/3.

`G1TwoChainParity.lean` EXTRACTS the parity information missing from
unrestricted two-chain arithmetic. If either affine seed is even,
deleting the other seed leaves a same-parity subtuple and constructs an
actual half child, without criticality. Thus the G1 residual has BOTH
seeds odd; full cyclic units are not required. Its corner sides have
the same parity. If a side is `2^t`, t is below both arm lengths and
`2^(t+1)|N`, the other side is `2^t*v` with v ODD: exact matched dyadic
valuation, not only evenness. A common-divisor corner theorem supplies
this uniformly. The final critical G1 consumer retains the original
tuple, actual chains, both odd seeds and the small same-parity corner.
Ten declarations; full 15,168-job build; all 3,579 axiom lists standard-
only; 1,658 tests pass. Actual valid half children, nonunit odd seeds,
growing-depth congruences and essential depth/divisibility/oddness guards
pass. No search result is a proof premise. Next eliminate axis corners
and consume the interior cyclic relation. The sharp residual band is
not closed; SAME three unrestricted OPEN global gates, 0/3.

`TwoChainAxis.lean` eliminates ALL odd-seed axis corners in dimensions
k>=6. An actual nonzero axis relation inside the rectangle is the seed's
EXACT additive order, by uniqueness. Odd canonical seeds have odd index
over that order, including nonunits. Packing forces index >=2^A, hence
>=2^A+1. The uniform all-arm inequality
`(2^A+1)*(A+L+1-2^A)<=2^L` for A,L>0 and A+L>=6 then forces the
FULL binary bound `2^(A+L)<=N`. Both axis orientations are therefore
excluded below binary size. The final original critical G1 consumer
extracts a STRICTLY INTERIOR odd-seed corner, retaining its same-parity,
dyadic-side and deficit-payment constraints. Seven declarations; full
15,169-job build; all 3,586 axiom lists standard-only; 1,696 tests pass.
Actual valid odd/even-modulus axis families, nonunit seeds, growing
all-split inequalities and the auxiliary k=5 cutoff guard pass. No
balance, unit, G2/G3 or search premise is used. Axis extraction is DONE
in this range; next joint binary-weight savings for the interior cyclic
relation. SAME three unrestricted OPEN global gates, 0/3.

`TwoChainSparseCorner.lean` strengthens interior corner arithmetic:
each side is a power of two or a sum of two powers, and at least one
is a single power. Hence at most THREE binary digits remain in total.
A three-coin complementary saving pays for the opposite side's extra
coin and produces a full-length rival. This is uniform in ANY abelian
group, with no popcount implementation or census premise. Unique odd
dyadic factors combine with the preceding parity theorem: in the stated
uncapped range the corner is square or (a,a*(1+2^r)), r>0. The final
original critical G1 consumer extracts the strict sparse interior corner,
retaining actual chains, both odd seeds, parity and full deficit payment.
Eight declarations; full 15,170-job build; all 3,594 axiom lists standard-
only; 1,742 tests pass. Explicit full-length rivals, growing complement
ranges and valid affine/nonunit square and three-digit controls pass.
Sparsity is not itself a contradiction, and capped valuations are not
silently included in the shape theorem. Next primitive relation order
and cyclic divisibility to consume these sparse shapes. SAME three
unrestricted OPEN global gates, 0/3; no extra global input.

`TwoChainRelationOrder.lean` EXTRACTS exact order from the unique
actual rectangle relation. Dividing by ANY common coefficient factor D
produces an element of order exactly D, in any abelian group: a smaller
order would yield a second nonzero rectangle relation. The gcd primitive
direction therefore has full gcd order. In cyclic groups D divides N.
For two odd seeds, an even divided coefficient sum forces D|N/2;
an odd sum forces N/D odd. Thus at N=2^(s+1)*q, q odd, a dyadic factor
2^t has t<=s in the even-direction case and t=s+1 EXACTLY in the odd
case. Capped valuations are retained, not assumed absent. No individual
unit or supplied order/calibration premise is used. Eight declarations;
full 15,171-job build; all 3,602 axiom lists standard-only; 1,775 tests
pass. Actual valid twisted-seed families exercise every common factor,
nonunit odd embeddings and BOTH parity branches. Growing exact orders
and validity/oddness guards pass. Next packing-slack divisibility and
actual boundary extraction from tight corner packing, followed by the
completed one-escape consumer. That closure is not yet proved. SAME
three unrestricted OPEN global gates, 0/3.

`TwoChainTightCorner.lean` CLOSES tight interior corner packing, with
DIRECT G1 half descent and FULL global/every-stratum class bounds.
Equality in packing gives an ACTUAL full cover by the retained rectangle.
Positive-relation and odd-axis exclusions force a boundary representation
with zero first coefficient. Full coverage makes the relation determinant
a modulus multiple, and its range fixes it to N; the boundary coefficient
is exactly the opposite corner side. Automatic capacity extracts one
escape, so the completed class bounds apply. Any critical tight two-chain
tuple admits actual half descent: even seeds already give parity deletion,
and odd seeds contradict the new bound. No G2/G3, child induction, unit
or primitive-span premise is supplied. The primitive gcd divides packing
slack; after eliminating zero slack, the remaining ORIGINAL two-escape
G1 corner satisfies `2^k+gcd(2^A-a,2^L-b)<=N+a*b`, retaining all odd-
seed, strict-interior, parity and sparse-side data. Twelve declarations;
full 15,172-job build; all 3,614 axiom lists standard-only; 1,818 tests
pass. Actual valid covers, determinant ranges, positive-slack families
and coverage/criticality guards pass. Tight-case propagation is DONE.
Next extract full seed span and control positive-slack boundary images;
SAME three unrestricted OPEN global gates, 0/3.

`TwoChainSlackClosure.lean` CLOSES the ENTIRE actual two-escape G1
branch for parent dimension k>=9, including ALL positive packing slack.
Near-binary packing inside a proper subgroup is impossible, so full
JOINT seed span is extracted from validity, not supplied as a premise.
Every represented boundary has determinant exactly N and slack
`(2^A-a)*(c-b)`; the binary axis inequality makes its capacity automatic.
A short exterior column has distinct residues and must meet the retained
rectangle when its height exceeds slack. Negative boundary coefficients
would yield a nonzero determinant below N. Thus actual counting extracts
one-escape closure in either orientation. For k>=9, small dyadic-sided
corners satisfy `a*b<=max(2^A-a,2^L-b)`, while subbinary slack is below
`a*b`; the only dimension-ten quadratic exceptions (5,6)/(6,5) have no
dyadic side. FULL global and EVERY exact-stratum bounds now hold for ALL
interior two-chain corners in this range, without odd-seed or slack
premises. The original critical tuple with at most two affine escapes
admits actual half descent, without corner/span/unit/G2/G3/child-bound
inputs. Twenty declarations; full 15,173-job build; all 3,634 axiom lists
standard-only; 1,865 tests pass. Forty-seven new regression checks cover
general arithmetic, positive-slack identities, actual valid full-span
families and essential hypothesis guards; no census is a proof input.
A remaining k>=9 G1 counterexample needs at least THREE actual escapes at
EVERY offset. Next consume bounded two-escape parents below nine, then
the unrestricted multi-escape residual. SAME three global OPEN gates, 0/3.

`G1TwoEscapeClosure.lean` completes ACTUAL two-escape G1 in EVERY
dimension, removing all bounded cases left by the tail theorem.
For dimensions 6--8, parity bounds the small corner's excess over a
relation side by four, while exact even-stratum criticality forces
binary deficit strictly greater than four. Exterior-column counting
consumes the slack. Injectivity only on the ACTUAL tuple doubles gives
an m-element layer outside the anchored `2^m` cube in ANY finite abelian
group; this closes the four-coordinate G1 base without an escape-count
assumption. At five, an extracted actual three-term chain is consumed
by the completed two-extra multiplier theorem, including nonunits and
arbitrary reindexing. The original critical tuple with at most two
affine escapes now admits half descent with no size, corner, span,
seed, child-bound or G2/G3 premise. `PrimitiveThreeEscapeDeleteStep`
is proved EQUIVALENT to the existing primitive G1 gate: only parents
k>=5 with at least THREE genuine escapes at EVERY affine offset remain.
Both `stratum_lower_bound_of_primitive_threeEscapeDeleteStep` and
`global_lower_bound_of_primitive_threeEscapeDeleteStep` feed this input
into the existing strong-dimension induction with exactly the SAME
G2/G3 assumptions. Fifteen declarations (fourteen theorems, one equivalent
G1 definition); full 15,174-job build; all 3,649 axiom lists standard-only;
1,917 tests pass. Fifty-two new arithmetic, actual-family and hypothesis
guards are not Lean proof inputs. ALL two-escape G1 work is DONE. Next
unrestricted three-or-more-escape actual growth and extraction. SAME
three global gates OPEN, 0/3; no fourth gate or child premise is added.

`G1ThreeEscapeCycle.lean` CLOSES EVERY critical three-escape actual-cycle
G1 case, with no cycle-size or outsider-count exceptions. Injective actual
doubling removes the artificial collision-deletion loss: all-depth growth
is `2^t*k < m+k+e*(t*2^t-(2^t-1))` for ANY actual escape count e. The
condition 5e<=2m+6 extracts the completed cutoff k<=m+1; FULL global,
every-stratum and original-G1 consumers are proved for this growing-arity
class. A stronger even-index parity argument handles k=m+2 uniformly:
N+4>=2^n. A hypothetical larger deficit leaves half-index 2^(k-1) or
2^(k-1)+1; the first has zero even holes plus one deletion endpoint, the
second is odd and pays one even hole with NO extra endpoint. Both violate
the strict first-layer bound. Thus FULL global and every positive exact
stratum are proved for ANY even-modulus actual cycle with k<=m+2,
without an escape-count or tuple-injectivity premise. Failed G1 half
descent supplies injective doubling; three escapes force this cutoff.
Singleton cycles are consumed by the completed four-coordinate base.
The original no-half three-escape data are therefore injective and
ACYCLIC. Fifteen theorems; full 15,175-job build; all 3,664 axiom lists
standard-only; 1,965 tests pass. Forty-eight new actual-family, uniform
endpoint, rank-budget and essential-hypothesis checks are not Lean proof
inputs. No finite cycle exception remains queued. Next actual acyclic
three-chain extraction and arithmetic; SAME three global OPEN gates, 0/3.

`AffineChainForest.lean` now EXTRACTS the complete acyclic forest for ANY
finite escape set, retaining every actual coordinate, arrow and original
endpoint. The geometry is valid in any abelian group and does not assume
validity, a normal form, unit seeds, or fixed arity. The original critical
three-escape G1 residual supplies EXACTLY three genuine full chains and
at least TWO odd seeds. Independently, a general cube-index argument
shows that EVERY translate of ANY positive-length subbinary valid tuple
generates the whole ambient finite group. Thus every actual forest has
full JOINT seed span in this regime. Whole-tuple span is not the EVERY-
deleted-subtuple span condition in primitive G1. Ten theorems; full
15,176-job build; all 3,674 axiom lists standard-only; 2,062 tests pass,
including 97 new all-arity, actual-family and essential-hypothesis checks.
Actual three-chain arithmetic is next; its geometry is no longer an
assumption. All three unrestricted G1/G2/G3 gates remain OPEN, 0/3.

`ChainForestRelations.lean` proves arbitrary-arity coin refinement and
actual integer-weight rivals. Balanced-support mixed relations are
impossible at ANY arm lengths; other signed relations can increase only
arms with binary width below the original length k. If all arms have
width at least k, box fibres are ordered. Subbinary cardinality EXTRACTS
a nonnegative zero relation with corner-side sum <=k+r-1 and at least one
power-of-two side. If 2k<=sum(2^L_i-1), the relation is UNIQUE and removing
its one upper corner leaves an injective box: `2^k<=N+product a_i`.
For three long arms that extra width condition is automatic. The
ORIGINAL critical three-escape G1 consumer retains genuine endpoints,
seed parity and full span and supplies either a short arm or this actual
small dyadic-sided corner paying for the whole binary deficit. Sixteen
theorems; full 15,177-job build; all 3,690 axiom lists standard-only;
2,145 tests pass, including 83 new
refinement, signed-budget, actual packing and essential-hypothesis guards.
Next consume exact boundary coverage, positive slack and short arms.
The product bound alone is NOT the sharp conjecture; unrestricted
G1/G2/G3 remain OPEN, 0/3.

`ChainForestBoundary.lean` CLOSES the ENTIRE tight long-forest G1 branch,
including all axis corners. Arbitrary-arity complement savings force a
nonzero capacious positive boundary representation to have exactly one
coefficient, a power of two. Exact packing EXTRACTS full box coverage.
The unique relation then forces a represented boundary to have zero
pivot coefficient and be nonzero, yielding an ACTUAL endpoint rejoin.
Any nonzero relation in at least three long chains automatically has
two supported coordinates and enough width; no interiority is assumed.
The direct ORIGINAL-G1 consumer proves half descent for every tight
long three-chain forest. Genuine terminal forests at arbitrary arity
>=3 have STRICT packing slack. Original no-half three-escape data now
supply a short arm or a small dyadic-sided corner with positive slack.
Fourteen theorems; full 15,178-job build; all 3,704 axiom lists
standard-only; 2,210 tests pass, including
65 new actual rival/rejoin, axis-corner and essential-hypothesis guards.
Next positive slack and short arms; tight coverage is no longer queued.
The unrestricted G1/G2/G3 gates remain OPEN, 0/3.

`ChainForestSlack.lean` charges every supported genuine endpoint as a
DISTINCT residue missing from the ENTIRE binary box. General avoided-set
packing therefore gives `S>=m`, where S=N+product a_i-2^k and m is the
number of supported relation coordinates. The direct original G1
consumer closes insufficient support slack, including all one-unit
cases and interior two-unit cases, uniformly in dimension. Every common
relation factor D has EXACT divided-direction order, divides N and S,
and gives `S>=max(D,m)`. These mechanisms have arbitrary arity and do not
assume units, all-odd seeds, a supplied gcd, order or determinant. The
original three-escape no-half data extract either a short arm or the
support- and divisor-charged actual corner data. Ten theorems; full
15,179-job build; all 3,714 axiom lists standard-only; 2,277 tests pass,
including 67 new growing-arity genuine nonunit, missing-boundary,
exact-order and essential-hypothesis guards. Larger charged slack and
short arms remain; unrestricted G1/G2/G3 are still OPEN, 0/3.

`ChainForestParity.lean` gives exact parity-resolved forest packing.
All supported genuine boundaries are EVEN, so actual slack S and the
corner bias B satisfy `S+B>=2m`, where B is the product of even-seed
corner sides and odd-seed side parities. An odd number of odd seeds
forces B=0 at arbitrary arity. In particular every all-odd three-chain
forest has S>=2m; the exactly-two-odd-seed correction is retained.
Generic target-fibre packing and exact zero-corner transport supply
the counts without unit, all-odd, interior or census assumptions.
Direct original G1 half descent consumes insufficient parity slack;
the actual residual retains every prior support/divisor/order charge.
Eighteen theorems; full 15,180-job build; all 3,732 axiom lists standard-
only; 2,356 tests pass, including 79 new exact-count, growing genuine
all-odd/nonunit and essential-hypothesis guards. Larger slack, short
arms and the unrestricted G1/G2/G3 gates remain OPEN, 0/3. Next examine
axis-corner global volume bounds and interior exterior-face counting.

`ChainForestAxis.lean` closes ALL long-forest axes for the SHARP GLOBAL
lower bound, at arbitrary arity in every finite abelian group. The small
side sum forces the axis width and entire corner volume to equal dyadic
tuple length k. Actual packing gives globalBound k<=card G; genuine
endpoints make it strict. Non-dyadic lengths have no axis at any modulus.
Original subglobal three-escape data now extract an INTERIOR corner or
short arm, with prior charges retained. High exact-stratum axis G1 half
descent is proved; low exact strata at dyadic lengths remain open and
are not implied by the global envelope. Eight theorems; full 15,181-job
build; all 3,740 axiom lists standard-only; 2,427 tests pass, including
71 new growing-arity actual equality, exact retained-box, nonunit/
translation and scope guards. Next interior exterior-face counting,
short arms and lower-stratum dyadic axes. Global axes are CLOSED;
unrestricted G1/G2/G3 remain the SAME three OPEN gates, 0/3.

`ChainForestExteriorPacking.lean` now proves the BINARY bound
`2^n<=card G` for every genuine long three-chain forest with n>=67,
in any finite abelian group. Its arbitrary-arity column theorem charges
`min(d_j,2^(L_j-4)+1)` distinct residues missing from the whole binary
box. A putative column collision has zero pivot and a strict shifted
coordinate deficit; that small shift saves two coins, producing an
actual full-length rival. For three chains, a proved exponential-versus-
cubic inequality makes the charge exceed the entire corner volume in
the stated dimension range. No unit, parity, cyclicity, or supplied
relation is assumed in the final theorem.

Direct original G1 half descent now handles this entire class in EVERY
even stratum. Original no-half three-escape data at length at least 67
extract an actual SHORT arm, retaining genuine endpoints, two odd seeds
and joint span. All long positive-slack cases in that range are closed.
Twelve theorems; full 15,182-job build; all 3,755 audited declarations
have only standard axioms or none; 588 targeted forest tests pass, including 223 new independent rival, column and scope checks. Smaller
long forests, short arms, higher escapes and unrestricted G1/G2/G3 remain
open. The conjecture is not proved; no new global premise is introduced.

`ChainForestTrimmedPacking.lean` includes ALL short arms in a uniform
near-binary bound for every actual r-chain forest in every finite abelian
group: `2^n<=card G+binomial(n+r-1,r)`. The signed coin-budget theorem
puts one endpoint of every box collision into the upper simplex of
points whose total distance from the top is below n. Its complement is
injective, and adding a slack coordinate gives the stars-and-bars count.
An additional bound uses `product min(n,2^L_i)` to retain actual short
widths. An avoided-set variant and an actual acyclic-map extraction
consumer apply at arbitrary arity, with no unit, parity, all-long,
genuine-endpoint or supplied-relation premise in the forest bound.

For original THREE-escape G1 data, failure of half descent now implies
`2^n<=N+binomial(n+2,3)` even with short arms. Direct half descent closes
all moduli below this window. Every stratum with
`2^v₂(N)>binomial(n+2,3)` also closes for this class in every dimension.
The remaining near-endpoint window has an actual short arm at n>=67;
smaller dimensions can still have long forests. Thirteen new theorems;
full 15,183-job build; all 3,768 audited declarations use only standard
axioms or none; 692 targeted forest tests pass, including 104 new short-arm,
incomparable-fibre, simplex-count and arithmetic checks. The sharp
linear deficit, higher-escape extraction and unrestricted G1/G2/G3
remain open. No additional global premise is introduced.

`ChainForestCollisionProfiles.lean` now bounds the number of actual
small collision profiles. The exact joint law is
`dist_top(p)+weight(q)<n` or its reversal. High-weight points are
injective; if the box diameter is at least 2n-1, low points are injective
too and every fibre has at most two points. Every three-chain forest
satisfies this diameter condition at n>=7.

With K_i=2^L_i, the profile family P consists of all w with
`0<=w_i<=2*(K_i-1)`, `sum w_i<n` and
`sum w_i*x_i=sum (K_i-1)*x_i`. The actual lower collision endpoints for w
form the rectangle `max(0,w_i-(K_i-1))<=q_i<=min(K_i-1,w_i)`. Different
profiles have disjoint rectangles. A profile is uniquely determined by
its overflow set `{i : K_i-1<w_i}`, since equal overflow sets share a
canonical lower point and would have equal high endpoints. Only short
arms can overflow. Thus there are at most `2^(number of short arms)`
profiles; for three chains of length n>=10 there are at most FOUR.

Removing the profile rectangles gives the explicit relation-sensitive
bound

    2^n <= card G + sum_{w in P} product_i min(w_i+1,2*(K_i-1)+1-w_i).

The family is nonempty in every subbinary forest. An original G1
consumer extracts one to four profiles from three-escape no-half data,
retaining genuine endpoints, at least two odd seeds and full joint span.
The profile volumes still require the sharp estimate; this theorem
classifies the residual rather than closing it. Nineteen new theorems,
including the strengthened joint law in `ChainForestTrimmedPacking.lean`.
No additional assumed gate; unrestricted G1/G2/G3 remain open.
Full 15,184-job build passed. All 3,787 audited declarations use only
standard axioms or none, including all nineteen new theorem names.
796 targeted forest tests pass, with 104 new independent checks of
actual profile geometry, mixed collisions, nonunits and thresholds.

`ChainForestTwoLongArms.lean` extends the missing-column argument to
forests with arbitrary companion arms. Joint-distance collisions force
the exterior representation's own-axis coefficient to vanish if
K_a>n and K_j>n+t. At a subbinary modulus, an actual small profile rules
out a zero boundary in every arm with K_a>=2n+1: that period would
create distinct high-box points with equal value. A nonzero represented
genuine boundary would be an actual dyadic rejoin. The remaining tiny
shift therefore constructs a full-length rival, making the entire
column of `2^(L_j-4)+1` distinct residues unavailable to the box.

The binomial packing charges this column with no width condition on
other arms. For THREE chains of length n>=67, the longest arm supplies
the exponential charge automatically. Thus TWO genuine arms of width
GREATER THAN 2n force the BINARY bound, even if the third is short.
Original G1 half descent closes this class in every even stratum.

Every remaining original three-escape no-half case in that range now
has two companions of width at most 2n and a dominant chain of length
at least `n-2*floor(log_2(2n))`. An explicit embedding extracts its
coherent SI prefix `g(e i)=(2^i-1)*c+d` in the ORIGINAL modulus, allowing
nonunit c. The preceding forest consumer preserves genuine endpoints,
at least two odd seeds and joint span. Thirteen new theorems. Bounding
the logarithmic extras together with the actual one-to-four-profile
family is still required; this does not imply the completed three-extra
hypothesis. The sharp conjecture and unrestricted G1/G2/G3 remain open.
Full 15,185-job build passed. All 3,800 audited declarations use only
standard axioms or none, with every new theorem name audited. All 924
targeted forest tests pass, including 128 new independent checks of
short-arm geometry, nonunits, prefix identities and theorem scope.

`ChainForestDominantQuotient.lean` now proves exact companion-fibre
balance. Write K=2^L_j and B=2^(n-L_j). For ANY subgroup H containing
the dominant seed, a quotient fibre with m companion points supplies
(K-n)*m distinct residues through the high-coordinate interval [n,K).
At subbinary group size and K>=n*(B+1), one extra unit of quotient
rounding would exceed 2^n. Every quotient fibre must have the same size,
so `|G/H|` divides B. In particular the dominant seed subgroup has a
power-of-two index bounded by the number of companion coordinates.

For the remaining genuine three-chain class at n>=67 the threshold is
automatic: the companion widths give B<=4n^2 and the largest arm gives
K>=16n^3. In the original cyclic group the dominant multiplier satisfies
`gcd(N,x_j.val)=2^e`. If it is odd, it is a UNIT; for N=2^s*q with q odd,
it is coprime to q and its additive order contains q, even when it is
not a unit. The original three-escape no-half consumer preserves all
this data with genuine endpoints, two odd seeds, full joint span and
logarithmic companions. Nine new theorems. The sharp bound for these
dyadic-index profiles and extras remains open, as do unrestricted
G1/G2/G3; no new assumed gate is introduced.
Full 15,186-job build passed. All 3,809 audited declarations use only
standard axioms or none, with every new theorem audited. All 1,121
targeted forest tests pass, including 197 new independent checks.

`ChainForestBalancedAxis.lean` proves that a uniformly distributed box
in a nontrivial cyclic group has an actual nonzero seed annihilated by
its axis width. The proof factors the standard complex character sum;
exact balance makes the total zero, so one geometric-sum factor vanishes.
This works for arbitrary positive widths and any number of axes, without
finite computation as a premise. Exact dominant companion balance also
passes through any surjective homomorphism killing the dominant seed.

For the actual three-chain forest, an even dominant seed leaves TWO ODD
companions. Reduction modulo its already-proved index d=2^e makes both
companion seeds units. A wrapping axis therefore gives d | 2^L_a for
some actual companion a. An odd dominant seed already has d=1. Thus the
original k>=67 three-escape no-half consumer now extracts

    gcd(N,x_j.val)=2^e <= 2k,       e <= floor(log_2(2k)),
    e=0 OR e<=L_a for some a!=j.

This improves the previous bound by the product of companion widths to
one companion width, while retaining the SAME original forest, genuine
endpoints, two odd seeds, full joint span, logarithmic extras, and odd-part
coprimality/order information. Eight new theorems. The sharp profile/extra
estimate and unrestricted G1/G2/G3 remain OPEN; no new gate is introduced.

Full 15,187-job build passed. All 3,817 audited declarations use only
standard axioms or none, including all eight new theorem names. All 1,332
targeted forest tests pass, including 211 new exact-count checks and
counterexamples guarding uniformity, positive widths, and odd-seed scope.

`ChainForestProfileFibres.lean` removes all actual profile rectangles
and proves injectivity of the remaining box. Packing now works inside
ANY finite target set, with any avoided residues charged there. This
uses the arbitrary-arm joint collision law and has no all-long premise.

At even modulus with at least one odd seed, the ordinary binary box is
exactly balanced between parity classes. Write E and O for the sums of
even and odd lower-point counts across the actual profile rectangles,
and V for their total volume. Lean proves

    2^k <= N+2E,                 2^k <= N+2O,
    E+O=V,                      2^k+|E-O| <= N+V.

Thus parity imbalance is an additional exact charge on the deficit;
a profile family concentrated in one parity class cannot pay the other
class's deficit. For N=2^(s+1)*q<2^k, E and O must EACH be at least 2^s.
An original three-escape no-half consumer extracts both bounds at k>=10,
retaining one to four profiles, the actual forest, genuine endpoints,
two odd seeds, joint span, and the existing volume/dyadic gap bounds.

Eight new theorems and one definition. This strengthens the short-arm
profile constraints; it does not yet provide the sharp linear deficit
or close unrestricted G1/G2/G3. No new assumed gate is introduced.

Full 15,188-job build passed. All 3,826 audited declarations use only
standard axioms or none, including all nine new declarations. All 1,370
targeted forest tests pass, including 38 new actual-fibre, short-arm,
parity-imbalance, and hypothesis-counterexample checks.

`ChainForestProfileBias.lean` computes the previously abstract E-O
correction from the actual profile coordinates. For a profile w, write
S_i=min(w_i+1,2*(K_i-1)+1-w_i) and lo_i=max(0,w_i-(K_i-1)). Its bias is

    B_w = (-1)^sum(lo_i*x_i.val)
          * product_i (S_i if x_i is even; 0 if S_i is even; 1 otherwise).

Lean proves that B_w is exactly the even lower-point count minus the odd
lower-point count. The complete-family bound becomes

    2^k + |sum_w B_w| <= N + sum_w product_i S_i.

One odd coordinate at an odd seed makes B_w zero. If the NUMBER of odd
seeds is odd, the actual profile relation forces this case for EVERY
profile, including overflow in short arms: E=O exactly. Thus the all-three-
odd branch gets no extra charge from this parity correction and still
needs the sharp profile/carry estimate.

With exactly two odd seeds and an EVEN dominant seed j, the remaining
profiles have even coordinates on both companions. They contribute
B_w=(-1)^(number of overflow coordinates)*(w_j+1); all other profiles
contribute zero. The dominant axis cannot overflow. Its gap charge is
therefore the absolute alternating sum of at most FOUR compatible heights.
More generally, only overflow at ODD seeds changes the sign, while every
even seed retains its full rectangle side. Overflow at a short even seed
must NOT be counted as a sign change.

Thirteen new theorems and one definition. These are identities and a
stronger explicit necessary bound on the same extracted forests, not a
proof of the sharp global deficit. Unrestricted G1/G2/G3 remain OPEN.

Scope guard: (1,2,4,13,20) modulo 40 is valid, with three genuine chains
of lengths (3,1,1), but it has profiles (0,0,0) and (0,0,2), each of bias
+1, and the last short-arm boundary is zero. Genuine endpoints alone do
not imply a unique profile or nonzero short boundaries. This example is
ABOVE binary (40>32), so it does not refute a subbinary refinement.

Full 15,189-job build passed. All 3,840 audited declarations use only
standard axioms or none, including all fourteen new declarations. All
1,411 targeted forest tests pass, with 41 new exact-count checks of
shifted rectangles, signed heights, actual cancellation and scope guards.

`ChainForestProfileReflection.lean` reflects an actual small profile w
about the all-ones weights T_i=2^L_i-1. The vector X_i=2*T_i-w_i represents
the SAME distinguished sum and has total weight greater than k. Validity
therefore forces EVERY representation of X to use more than k coins.
This needs neither an all-long nor a box-diameter hypothesis.

A reflected coordinate saves a coin at overflow, costs at most one extra
coin strictly below its top, and saves that extra coin unless w_i+1 is a
power of two. Writing O for overflow coordinates and D for strict
underflow coordinates with a dyadic side, Lean proves the all-arity law

    |O| < |D|.

Consequently a THREE-chain profile overflows AT MOST ONE arm, in EVERY
dimension. If it overflows arm a, the complete shape is rigid:

    w_a+1 = K_a+2^e_a,
    w_i+1 = 2^e_i < K_i       for both i!=a.

A non-power overflow excess would save a second coin and produce an
actual full-length rival. Thus an overflowing rectangle has one side
K_a-2^e_a and two power-of-two sides.

For a wide three-chain box, profiles number at most one plus the number
of short arms. At k>=10 this improves FOUR to THREE profiles. Original
three-escape no-half data now extract ONE to THREE profiles with the
entire dyadic overflow shape, genuine endpoints, two odd seeds, joint
span, both parity lower bounds, and the existing volume/dyadic gap bounds.
In the even-dominant bias formula there is no double-overflow positive
term: only the no-overflow contribution and up to two negative compatible
heights remain. The sharp volume/carry estimate and unrestricted G1/G2/G3
are still OPEN; no new gate is introduced.

Eleven new theorems and one definition. The three-chain restriction is
essential: the actual valid six-chain tuple (4,5,7,11,19,35) modulo 60 has
profile (2,0,0,0,2,1), with two overflows and three dyadic underflows.

Full 15,190-job build passed. All 3,852 audited declarations use only
standard axioms or none, including all twelve new declarations. All
1,448 targeted forest tests pass, including 37 new reflection, dyadic-shape,
explicit-rival and higher-arity scope checks. The existing 104 profile
tests also pass with their three-profile assertion tightened.

### 2026-09-07: compatible overflow strips and a singleton binary bound

`ChainForestProfileStrips.lean` makes the even-dominant overflow geometry
explicit. Write K_i=2^L_i and suppose K_j>=k. If an actual three-chain
profile w has even coefficients on the two companions and overflows a,
reflection forces

    a!=j,  w_a=K_a,  w_b=0,  w_j+1=h=2^e,  K_a+h<=k.

Its lower rectangle is exactly the strip 0<=q_j<h, 1<=q_a<K_a, q_b=0,
of volume (K_a-1)*h. In an even modulus, with an even dominant seed and
two odd companions, its parity bias is -h. A coexisting no-overflow
profile v must have v_a=0, by disjointness of the actual lower rectangles
(the coexistence statement requires the already-proved wide-box bound).

If the entire actual profile family is this ONE strip, the explicit
parity packing theorem gives

    2^k <= N+(K_a-2)*h.

In particular, a length-one overflowing companion forces the BINARY
bound 2^k<=N. This closes that singleton-profile subclass, without an
all-long, genuine-endpoint, or box-diameter premise. It does not assert
that every residual profile is compatible, or that a no-overflow profile
exists. The valid genuine forest (2,4,8,33,45) modulo 50 has only profile
(1,0,2): a height-two strip, bias -2, and no no-overflow profile. Its
modulus is above binary. An odd dominant seed need not have negative
strip bias, as the checked modulus-32 mixed-parity example shows.

Seven public theorems, plus a private arithmetic helper. Full 15,191-job
build passed; all 3,859 audited declarations use only standard axioms or
none, including all seven new exports. All 1,465 targeted forest tests
pass, including 17 new actual-validity, strip, coexistence, permutation,
and scope checks. The sharp general profile/carry estimate and
unrestricted G1/G2/G3 remain OPEN; no new gate is introduced.

### 2026-09-07: every dominant quotient class needs an actual profile point

`ChainForestProfileQuotient.lean` combines exact companion balance with
injectivity outside the actual profile rectangles. For ANY number of
arms, assume the existing dominance threshold

    k*(2^(k-L_j)+1) <= 2^L_j.

Below binary, the profile lower rectangles must meet EVERY coset of
EVERY subgroup H containing x_j. If one coset has no removed profile
point, its whole balanced box fibre injects into that coset. Multiplying
this capacity by the subgroup index gives 2^k<=|G|, a contradiction.
This uses actual tuple validity and needs no all-long, wide-box, cyclic,
or parity hypothesis. At k>=67 the threshold is already available for
the surviving genuine three-chain residual.

The cyclic consumer strengthens the preceding strip exclusion. With
odd companions and dominant index d=gcd(N,x_j.val), any compatible
overflow strip with K_a<=d misses the ZERO quotient class: its only
nonzero companion coordinate ranges from 1 to K_a-1 and its seed is a
unit modulo the dyadic index d. Consequently, if EVERY actual profile
is such a strip, the BINARY bound holds. Several strips cannot repair
the missing class. No singleton or length-one assumption is needed.

Thus a remaining subbinary three-chain forest with odd companions must
have a no-overflow profile, an incompatible profile, or a compatible
overflow on an arm WIDER than the dominant index. This disjunction is a
consequence of the actual-forest consumer, not an additional global gate.
The sharper quantitative mass in each quotient class and endpoint/carry
restrictions remain to be used. The global conjecture and unrestricted
G1/G2/G3 remain OPEN.

Three public theorems. Full 15,192-job build passed; all 3,862 audited
declarations use only standard axioms or none, including all three new
exports. All 1,481 targeted forest tests pass, including 16 new actual
profile/coset checks and scope guards. Actual examples confirm that
removing dominance or the subbinary premise can lose a quotient class;
even companion seeds can make a narrow strip hit zero.

### 2026-09-07: quantitative mass in every dominant quotient class

`ChainForestProfileQuotientMass.lean` strengthens coset coverage to a
separate numerical deficit bound in EACH class. Under the existing
threshold k*(2^(k-L_j)+1)<=2^L_j, let H contain x_j, let d=|G/H|,
and let M_r count actual profile lower points whose values lie in r+H.
Lean proves, for ANY number of arms and EVERY r,

    2^k <= |G|+d*M_r.

The full ordinary-box fibre has exactly 2^k/d points below binary: it
splits into the entire dominant axis and the exactly balanced companion
fibre. Packing that fibre outside the actual profile rectangles gives
the bound. It also descends through any surjective homomorphism killing
x_j. No wide-box, all-long, parity, or genuine-endpoint premise is added.

For a cyclic modulus, d=gcd(N,x_j.val), and `forestProfileResidueMass`
counts each class directly by reduction of the actual evaluated residue.
The gcd-scaled bound uses that actual d, without supplying its dyadic
form. At N=2^t*q with q odd and N<2^k, Lean extracts

    d=2^e,  e<=min(t,k-L_j),  M_z>=2^(t-e) for EVERY z modulo d.

Thus nonempty coverage alone can be insufficient: the sharp forest with
lengths (1,1,10), seeds (1,2,4), and N=4088 has d=4 and exactly TWO
profile points in every class. One point per class cannot pay its gap.

Eight theorems and one definition. Full 15,193-job build passed; all
3,871 audited declarations use only standard axioms or none, including
all nine new declarations. All 1,493 targeted forest tests pass, with
12 new exact full-box/profile counts, saturation checks, and a dominance
scope guard. The sharp general profile/carry estimate and unrestricted
G1/G2/G3 remain OPEN; no new gate is introduced.

### 2026-09-07: exact strip masses and the full dominant-index charge

`ChainForestProfileStripMass.lean` computes the zero-class contribution
of a compatible overflow strip. If its height is h and overflow width
K_a, projection kills the dominant seed and makes the odd companion a
unit modulo d. Thus its zero-class points are exactly the positive
multiples of d along that arm:

    M_0(strip)=h*floor((K_a-1)/d).

For dyadic d and K_a, d*floor((K_a-1)/d)=K_a-d, with NATURAL subtraction.
Under the existing dominance threshold, actual validity supplies the
dyadic dominant gcd d=gcd(N,x_j.val). A singleton compatible overflow
profile therefore gives the full quotient correction

    2^k <= N+(K_a-d)*h.

This extends the parity-based (K_a-2)*h charge to the entire actual gcd.
More generally, if EVERY actual profile is a compatible overflow strip,

    2^k <= N+sum_profiles (K_a-d)*h.

The formal statement sums over each profile's actual overflowing arm;
reflection proves that arm is unique. Several strips are included, and
an arm with K_a<=d contributes zero. The index-based binary exclusion
from the preceding milestone is now the zero-charge case of a numerical
bound. Profiles with no overflow, incompatible coefficients, or three
odd seeds still need the remaining structural analysis; no global gate
is closed by this calculation.

Eight theorems. Full 15,194-job build passed; all 3,879 audited declarations
use only standard axioms or none, including all eight new exports. All
1,521 targeted forest tests pass, with 28 new exact-count and scope checks.
Actual genuine examples include lengths (3,2,1), seeds (4,23,115), N=120,
and profile (0,4,0): its width-four strip has zero mass modulo d=4. These
examples are above binary and are not evidence of global closure.
The sharp unrestricted estimate and G1/G2/G3 remain OPEN.

### 2026-09-07: sparse no-overflow sides from reflected coin savings

`ChainForestProfileSparseSides.lean` proves a uniform complement
representation saving FOUR coins whenever a positive side is not a sum
of one, two, or three binary powers. Adding the two top coins then makes
its reflected coordinate cost at most L_i-2. The other two coordinates
cost at most L_i+1 each, so an actual three-chain profile with such a
side would produce a full-length rival. No finite census is assumed.

The joint saving is stronger: if a strict-underflow side needs three
binary powers, BOTH other coordinates must be strict dyadic underflows.
Otherwise one additional saving again fits a reflected rival. Combining
this with the earlier overflow rigidity gives, for EVERY actual
three-chain profile in EVERY dimension, one of two patterns for w_i+1:

    one single power + two sums of at most two powers;
    one sum of three powers + two single powers.

Thus the three shifted coordinates use at most FIVE binary powers in
total. For a NO-OVERFLOW profile, w_i+1 are exactly its rectangle sides,
so this is a sparse classification of the remaining no-overflow shape.
For an overflow profile, the overflowing rectangle side is K_a-2^e,
which can have many binary digits: do not apply the five-power claim to
that rectangle side. The claim concerns the shifted coefficients.

Three powers on one side cannot be removed from the general theorem.
The actual tuple (1,2,4,8,16,2000,997975) modulo 1000000 is valid, has
three genuine chains, and has only profile (6,0,0), with sides (7,1,1).
The valid genuine profiles (2,2,0) at moduli 92 and 96 realize the other
maximal pattern, sides (3,3,1). These examples are ABOVE binary and do
not settle stronger subbinary restrictions. A four-digit side is also
checked against an explicit full-length reflected rival.

Eight theorems. Full 15,195-job build passed; all 3,887 audited declarations
use only standard axioms or none, including all eight new exports. All
1,546 targeted forest tests pass, with 25 new actual-validity, sparse-side,
complement-saving, and explicit-rival checks. The sharp general deficit
and unrestricted G1/G2/G3 remain OPEN; no additional gate is introduced.

### 2026-09-08: genuine short boundaries order coexisting profiles

`ChainForestProfileEndpoints.lean` excludes every nonzero small point on
another box face from a genuine escaping boundary. For any number of
chains, put K_i=2^L_i. If sum(K_i-1)>=2k-1, 0<=c_i<K_i,
c_a=0, and 0<sum c_i<k, then

    K_a*x_a != sum c_i*x_i.

No lower bound on the escaping arm's length is needed. Two positive
coefficients save the two coins needed to add its boundary; a sole
nonpower coefficient also saves two. Joint box capacity permits binary
refinement to a full k-term rival. The remaining single-power case would
rejoin an actual chain, contradicting the genuine endpoint. This extends
the older boundary exclusions that required k<=2*K_a-1.

In a valid genuine three-chain forest with this wide box and K_j>=k,
let w be an actual compatible overflow strip on arm a, and let v be an
actual no-overflow profile. The new consumer proves exactly

    v_j+1 < w_j+1, OR
    v_j=w_j, all v_i=0 for i!=j, and K_a*x_a=0.

The axis conclusion in the equality case is derived. If two compatible
strips on distinct short arms coexist with a no-overflow profile, that
profile is on the dominant axis and lies below both strip heights; both
boundary/height identities hold. Strictly lower profiles are not yet
excluded. Equality with zero boundary is necessary: the genuine valid
tuple (2,4,8,7,21) modulo 42 has profiles (0,0,0) and (0,0,2).
Smallness is also essential: the valid genuine forest (1,2,4,54) modulo
101 has short boundary 2*54=7, with represented weight 7>=k=4.

Ten theorems. Full 15,196-job build passed; all 3,897 audited declarations
use only standard axioms or none, including all ten new exports. All
1,581 targeted forest tests pass, including 35 new checks of genuine
small-face exclusions, equality examples, affine full-length rivals, and
the necessary smallness restriction. The sharp general deficit and
unrestricted G1/G2/G3 remain OPEN; no additional gate is introduced.

### 2026-09-08: repeated boundary rivals exclude two strips with a base

`ChainForestProfileStrict.lean` closes the strictly lower AXIS-base case
for k>=24 and dominant width K_j>=2k. If the base height is h and the
strip height is H>h, their actual profile relations give

    K_a*x_a + (H-h)*x_j = 0,    S=(h-1)*x_j.

Set c=H-h, D=K_a+c>=3, and m=floor(k/D)+1. Repeating that zero
relation gives weights X_a=m*K_a, X_j=m*c+h-1, all others zero.
Their total lies in [k,2k), and their evaluation is S. The short-arm
representation costs 2m coins. Uniformly for k>=24,
2k<2^(floor(k/3)-2), so the dominant weight costs at most
floor(k/3)-2 coins. The combined cost is at most k; binary refinement
constructs a full-length rival. This argument is uniform, not a census.

Consequently an axis base and a compatible strip in a genuine wide
forest have EQUAL heights and zero strip boundary. Two distinct
compatible strips already force any no-overflow profile onto the axis.
If both strips coexist with a base, both boundaries must therefore
vanish. In a group with at most one nonzero element of order two, a
genuine valid forest has at most one zero boundary: two would identify
their last actual entries. Thus in an EVEN CYCLIC group, TWO distinct
compatible strips CANNOT coexist with a no-overflow profile under the
stated length and width bounds. The previously extracted dominant-chain
inequality k*(2^(k-L_j)+1)<=K_j implies K_j>=2k.

A single zero-boundary strip with an equal base remains possible, even
at large lengths. Exact coin-interval checks verify genuine valid examples
at lengths 25 and 67, above binary. The unique-nonzero-two-torsion
restriction also matters: two genuine length-one chains in C2 x C2
can both have zero boundary. A non-axis base strictly below ONE strip,
incompatible profiles, and the sharp general deficit remain open.

Eight theorems. Full 15,197-job build passed; all 3,905 audited declarations
use only standard axioms or none, including all eight new exports. All
1,693 targeted forest tests pass, including 112 new uniform-budget checks,
affine full-length rivals, large genuine equality examples, and cyclic
endpoint checks. Unrestricted G1/G2/G3 remain OPEN; no new gate is added.

### 2026-09-08: a coexisting axis base forces a length-one strip arm

The repeated-boundary construction in `ChainForestProfileStrict.lean`
now permits zero dominant increment. It needs only K_a+c>=3, with
c>=0, rather than c>0. The previous positive-increment theorem remains
available with its original statement.

Apply the stronger construction to the zero boundary already forced by
an axis base and compatible strip. If L_a>=2, then K_a>=4, and repeating
that boundary alone gives weights X_a=(floor(k/K_a)+1)*K_a,
X_j=h-1, all others zero. Their coin cost is at most k and their total
weight is at least k, producing an actual full-length rival. Therefore,
under the existing k>=24, K_j>=2k and genuine wide-forest hypotheses,

    an axis base plus a compatible strip forces L_a=1,
    equal heights, and zero strip boundary.

This restriction holds in arbitrary abelian groups. Length-one examples
above binary at lengths 25 and 67 remain valid. The height of the
surviving strip, non-axis bases below one strip, incompatible profiles,
and the sharp general deficit still require further work.

Two new theorems; the existing positive-increment result is retained.
Full 15,197-job build passed; all 3,907 audited declarations use only
standard axioms or none. All 1,747 forest tests pass, including 54 new
explicit affine rivals for wider zero-boundary arms. Unrestricted
G1/G2/G3 remain OPEN; no additional gate is introduced.

### 2026-09-08: strip height at most two and four-point family closure

`ChainForestProfileHeights.lean` bounds the height left by the length-one
zero-boundary reduction. For an axis base and compatible strip under the
existing k>=24, K_j>=2k and genuine wide-forest hypotheses, both heights
are at most TWO. If h=2^e with e>=2, use m=floor((k-e)/2) copies of the
zero boundary and the dominant weight 2^e-1. Their coin cost is at most
k, while their total weight is at least k because 2^e>=e+2. Joint binary
refinement supplies the full-length rival, including the parity remainder.
The underlying height exclusion needs no dimension cutoff beyond its
explicit width and small-target budget.

Each of the two profile rectangles consequently has at most two points.
If the entire actual family consists of that axis base and strip,

    2^k <= card G + 4,    globalBound k <= card G.

This is a sharp GLOBAL bound for this profile-family class, in arbitrary
finite abelian groups. In an even cyclic group the family-exhaustion
premise can also be derived: if all actual profiles are compatible, an
axis base and any overflow leave exactly that base and one strip. Another
no-overflow profile has the same pattern and coincides with the base;
another strip is either identical or gives the excluded two-strip/base
configuration. Thus the compatible axis-base/overflow class is closed.

Both possible heights occur in genuine valid examples above binary,
including height one at length 67 and height two at length 68. Exact
coin-interval checks exhaust all full-length rivals and enumerate their
complete small-profile families. These examples show the height bound is
sharp in the general theorem; they are not subbinary counterexamples.
An axis-only family, incompatible profiles, non-axis bases below one
strip, and the sharp general deficit remain open.

Seven theorems. Full 15,198-job build passed; all 3,914 audited declarations
use only standard axioms or none. All 1,793 forest tests pass, including
46 new height-budget checks, explicit affine rivals, sharp large examples,
and exact family volumes. Unrestricted G1/G2/G3 remain OPEN; no new gate.

### 2026-09-08: even axis-base closure without assuming full compatibility

`ChainForestProfileEvenAxis.lean` removes the all-profiles-compatible
premise from an even-dominant axis-base class. With an even dominant seed
and odd companions, the target of an axis base is even. If one companion
coefficient of any profile is even, its other companion coefficient must
also be even, by reducing the actual profile relation modulo two.

A length-one companion makes its coefficient even in EVERY actual
profile. The no-overflow profile is the axis base by pattern uniqueness.
On an overflow at the length-one arm its coefficient is exactly two;
on an overflow at the other arm, reflection forces it strictly below
its top, hence zero. Parity then forces the remaining companion
coefficient even. Thus the entire actual family is compatible. This
compatibility theorem needs no genuine-endpoint premise or length-24
cutoff beyond its explicit wide-box and dominant-width hypotheses.

For k>=24 and K_j>=2k in a genuine forest over an even cyclic group,
this gives two sharp GLOBAL closures with an even dominant seed and odd
companions. An axis base plus a length-one companion and ANY overflow
satisfies 2^k<=N+4 and globalBound k<=N. An axis base plus just ONE
COMPATIBLE overflow also satisfies both bounds: the earlier theorem
forces that strip's arm to have length one, and full compatibility now
follows. No hypothesis on the remaining profiles or family exhaustion
is supplied in either closure.

Length one is essential for the compatibility lemma. The genuine valid
forest with lengths (4,2,2), seeds (2,299,31), modulus 506 has exactly
profiles (4,0,0) and (0,5,1); the latter is incompatible. Further examples
at moduli 514 and 518 have the same incompatible profile. All are ABOVE
binary. The remaining even-axis overflow case can therefore involve
only incompatible overflows with BOTH companion lengths at least two.
Axis-only families, non-axis bases, odd dominant seeds, and the sharp
general deficit still require further work.

Four theorems. Full 15,199-job build passed; all 3,918 audited declarations
use only standard axioms or none. All 1,838 forest tests pass, including
45 new permuted affine validity checks, genuine scope counterexamples,
and explicit reflected rivals. Unrestricted G1/G2/G3 remain OPEN.

### 2026-09-08: even-axis-only binary bound and full length-one closure

`ChainForestProfileAxisOnly.lean` closes the even-axis-only case by
packing the odd residue class. If every actual profile is concentrated
on an even seed's axis, every point of every removed lower rectangle
has even residue. The odd removed mass is zero. As soon as one seed is
odd, the odd half of the original binary box has size 2^(k-1), and its
packing gives the full BINARY bound 2^k<=N.

This theorem holds in EVERY arity, with no dominant-width, wide-box,
genuine-endpoint, or length-cutoff hypothesis. The profile family may
also be empty. In a wide forest with an actual axis base and no
overflows, pattern uniqueness derives the required axis-only family.
No height bound is imposed: genuine even-axis-only examples of height
seven are checked at lengths 7, 25, and 67. Odd-axis-only examples at
sharp subbinary moduli show why the even-seed premise matters.

Combining this with the overflow closure gives, at k>=24 and K_j>=2k
in genuine even cyclic three-chain forests with odd companions:

    an entirely compatible family with an even axis base satisfies
    2^k<=N+4 and globalBound k<=N, whether or not an overflow exists;
    an even axis base with ANY length-one companion satisfies both
    bounds, with no overflow-existence or compatibility premise.

Thus a remaining subglobal even-axis case must have an incompatible
overflow and BOTH companions of length at least two. An even-axis-only
case is closed outright. Odd dominant axes, non-axis bases, and the
remaining incompatible-profile geometry are still open.

Four theorems. Full 15,200-job build passed; all 3,922 audited declarations
use only standard axioms or none. All 1,871 forest tests pass, including
33 new all-arity odd-class injection checks, large genuine axis-only
examples, and sharp odd-axis controls. Unrestricted G1/G2/G3 remain OPEN.

### 2026-09-08: comparable-profile rigidity and a uniform zero-target bound

`ChainForestProfileOrder.lean` proves a uniform restriction on ANY two
actual small profiles: if v_i<=w_i for every i and v!=w, then at least
one changed arm has length ONE. The result holds in every arity and
abelian group, with no dimension, dominant-width, wide-box, parity, or
genuine-endpoint hypothesis.

The positive difference z=w-v is a zero relation. Put V=sum v_i,
Z=sum z_i>0, and q=floor((k-V-1)/Z). Since V+Z<k,

    q>=1,    V+q*Z<k<=V+2*q*Z.

If every changed arm has a second entry, the weights v_i+2*q*z_i
are represented by v_i seed coins and q*z_i actual doubled-seed coins.
Their total coin cost is STRICTLY below k but their total weight is at
least k. Binary refinement gives a full-length rival. A Mersenne weight
needs one coin per original chain entry, so the strict saving also
excludes the all-ones weight without a separate inequality premise.

Consequently, if EVERY arm has length at least two and v is an axis
profile at j, every other profile w satisfies w_j<v_j. This gives the
correct strict order for the remaining incompatible-overflow case,
without a length cutoff. The genuine examples (0,5,1) below the axis
profiles (4,0,0), (2,0,0), and (1,0,0) realize this order. Comparable
profiles with a length-one changed arm exist, so that exception matters.

A zero profile is then the ENTIRE family. Its rectangle has volume one
and parity bias one. At even modulus, if any seed is odd, parity packing
cancels that one-point correction and gives the BINARY bound 2^k<=N.
Thus every zero-target forest with all arm lengths at least two satisfies
this bound, in every arity. No even seed, genuine endpoint, wide box, or
length cutoff is required; two-chain examples with all seeds odd are
included. Other axis heights and the general deficit remain open.

Eight theorems. Full 15,201-job build passed; all 3,930 audited declarations
use only standard axioms or none. All 1,927 forest tests pass, including
56 new explicit affine rivals, genuine ordering and length-one controls,
and all-arity zero-target checks. Unrestricted G1/G2/G3 remain OPEN.

**Even-axis high odd-slab packing (2026-09-08).**
`ChainForestProfileSlab.lean` proves that, when every arm has at least two
entries, every removed ODD box point lies strictly below an actual base
profile supported on an EVEN seed axis j. The other profiles are strictly
lower on j; the base itself removes only even points. Thus all odd points
with p_j>=v_j remain injective. Exact parity counting of this truncated box
gives

```
2^n <= N + v_j * 2^(n-L_j).
```

This holds in every arity for an even modulus and at least one odd seed,
with no dominance, width, wide-box, or genuine-endpoint premise. If v_j is
outside the ordinary axis box, the inequality is automatic. The sharp
GLOBAL bound follows whenever v_j*2^(n-L_j)<=2^floor(log_2 n). In particular,
a coefficient-one base is closed when the companion volume fits this
allowance. This does not bound that charge in every remaining family;
positive bases with larger charge, odd axes, non-axis bases, higher escapes,
and unrestricted G2/G3 remain OPEN. No new gate is introduced.

**Upper corners above arbitrary profiles (2026-09-08).**
`ChainForestProfileUpperCorner.lean` extends the antichain law beyond axis
bases. If every arm has at least two entries, the translated upper corner
above ANY actual profile v is injective away from zero. A point in that
corner and a lower collision rectangle would force comparable profiles,
hence equality; the only possible intersection is the base v itself.
Consequently, in any finite abelian group,

```
product_i (2^(L_i)-v_i) <= card G + 1.
```

The differences are truncated natural differences, so an overflowing
profile gives an empty corner. At an even cyclic modulus, if some ODD seed
has an EVEN profile coefficient, the translated corner has balanced
parity. Its odd points avoid zero, improving the right side to N. This
includes non-axis profiles and all-odd seed families; it needs no width,
wide-box, dominance, or genuine-endpoint hypothesis. Genuine non-axis
examples verify both balanced and unbalanced cases. Odd Mersenne cycles
show that the general extra point and exclusion of the base are sharp.
The individual corner bound still needs a sharp joint charge to close all
remaining profiles. The unrestricted conjecture and G1/G2/G3 remain OPEN.

**Half-width rigidity for incompatible overflows (2026-09-08).**
`ChainForestProfileHalfSides.lean` sharpens the remaining even-axis case.
Let v be an actual axis base and w an incompatible overflow on companion a,
with k the other companion. Write K_i=2^(L_i). When all arms have second
entries, the box is wide, and n<=K_j, actual validity forces

```
w_a+1 = K_a + K_a/2,     w_k+1 = K_k/2,
v_j-w_j = 2^r,          w_j+1 = 2^s,
v_j+1 = 2^r + 2^s.
```

The proof shifts the original weights by w-v. These still represent the
original target and have enough total weight to refine to n coins. Their
companion costs are e+3 and f+1 when the original dyadic sides are 2^e and
2^f. Any side smaller than half its width saves a coin and constructs a
forbidden rival. A dominant drop needing two binary digits also saves a
coin and is impossible. The generic shift obstruction holds in every
abelian group and arity; the direct consumer derives all powers and their
positivity from actual even-axis data with odd companions. No genuine
endpoints or numerical length cutoff are required.

Genuine surviving examples have exactly n+1 coins in the shifted weights,
so the last coin cannot simply be discarded. The 90 new tests include
explicit full-length rivals at n=12,24,67 for both excluded mechanisms,
with coordinate permutations and affine shifts. The surviving half-width
families still need a sharp joint bound. The global conjecture and
unrestricted G1/G2/G3 remain OPEN; no new gate is added.

**Two incompatible overflows are excluded (2026-09-08).**
`ChainForestProfileDoubleOverflow.lean` proves that an actual even axis base
cannot coexist with incompatible overflows on both companion arms. The
half-width theorem supplies their shapes. Adding the two profile equations
then cancels the companion terms and gives

```
(2*K_j-H_a-H_k) * x_j = 0.
```

Here H_a,H_k are the overflow heights. If the base coefficient is V, strict
profile ordering gives H_a,H_k<=V<K_j. Adding V to this positive period
produces a weight z with K_j<=z<3*K_j representing the original target.
It costs at most L_j+4 dominant-chain coins. Both companions have at least
two entries, so this fits the original n-coin budget and refines to a
forbidden full-length rival supported on the dominant chain alone.

The generic half-shaped exclusion works in any abelian group. The direct
even-axis consumer derives the shapes from the actual profiles and needs
only all-arm length>=2, joint wide capacity, n<=K_j, and odd companions.
It has no subbinary, dominant-index, genuine-endpoint, or numerical length
cutoff premise. The 80 new tests check explicit full-length rivals at
n=11,12,24,67, with permutations and affine shifts, and sharpness of the
scalar coin bound. Combined with overflow-pattern uniqueness and the prior
compatible/length-one closures, the remaining subglobal even-axis family
is the base plus at most ONE incompatible half-width overflow. Closing
that pair, odd-axis and non-axis families, higher escapes and G2/G3 remains
OPEN; the unrestricted conjecture is not complete.

**Complete even-axis pairs and their quarter-box charge (2026-09-08).**
`ChainForestProfilePair.lean` now derives the complete remaining family.
For a genuine three-chain forest with n>=24, joint wide capacity,
K_j>=2n, an even dominant seed, odd companions and an actual axis base,
any modulus below the sharp global bound forces every arm to have length
at least two and the profile family to be exactly that base and ONE
incompatible overflow. No family-exhaustion or compatibility premise is
left to the caller. Same-arm overflow uniqueness and the opposite-arm
exclusion supply the final exhaustion step.

Writing H=w_j+1 for the overflow height, its half-width companion sides
have exact rectangle volume H*2^(n-L_j-2). The base removes only even
points, while the incompatible rectangle has equal even and odd masses.
The separate parity packing bound therefore gives

```
2^n <= N + H*2^(n-L_j-2).
```

This improves the earlier base-height slab charge by at least a factor
of four. The sharp global bound follows whenever this actual overflow
charge is at most 2^floor(log_2 n); a subglobal case extracts the complete
pair with a charge strictly greater than that threshold. The direct
conditional consumer handles short arms, compatible profiles and family
exhaustion internally. Larger charges are still OPEN.

The 54 new tests check exact odd masses and complete genuine families
under permutations and affine shifts. Genuine surviving pairs are
certified through n=67 and n=68 by checking ALL possible n-term multiset
representations via bounded companion weights and unique dominant lifts.
These above-binary examples show that the pair cannot simply be excluded
without an additional hypothesis. Odd-axis/non-axis families, higher
escapes, unrestricted G1/G2/G3 and the global conjecture remain OPEN.

**Half-profile midpoint phases and an odd-half closure (2026-09-08).**
`ChainForestProfileMidpoint.lean` proves a new obstruction for the surviving
pair. If the overflow height is at least two, every profile coefficient
is odd, so Y_i=(2^(L_i)-1+w_i)/2 is an integer. With K_j>=2n, this midpoint
has enough total weight to refine to n coins. Its overflowing companion
costs at most L_a coins and its other companion at most L_k-1; the dominant
coordinate costs at most L_j. Thus its total coin cost is STRICTLY below n.
If it represented the original target, it would give a forbidden rival.
The generic obstruction works in any abelian group, without an axis base
or genuine endpoints once the half shape and integral midpoint are supplied.

For an actual profile at N=2M, doubling the midpoint sum doubles the target.
Validity therefore forces the midpoint sum to be the target PLUS M. With
an even dominant seed and two odd companions, its parity gives

```
M % 2 = (2^(L_a-2) + 2^(L_k-2)) % 2.
```

Thus M is odd exactly when ONE companion has length two and the other is
longer. If both have length two, or both are longer, M must be even.
The direct even-axis consumer derives the half shape, integrality and
phase from actual profiles. There is no supplied midpoint-phase premise.

Combining this with complete-pair exhaustion closes a new sharp GLOBAL
case: genuine even-axis forests with n>=24, wide capacity, K_j>=2n,
odd companions of length TWO each, and an ODD half modulus M. Any residual
overflow must have height one, whose quarter-companion charge is four.
The 192 new tests construct explicit full-length midpoint rivals through
n=67,68, including two length-three companions, permutations and affine
shifts. Genuine height-two and height-one controls verify the nonzero phase
and the integrality cutoff. Even half moduli, other companion lengths,
other profile families, higher escapes and unrestricted G1/G2/G3 remain
OPEN; the global conjecture is not complete.

**Dominant index four with two short companions is closed (2026-09-08).**
`ChainForestProfileIndexFour.lean` closes the genuine even-axis GLOBAL
case with two length-two companions and gcd(N,x_j.val)=4, at n>=24,
wide capacity and K_j>=2n. All even-modulus strata are included; no odd
half-modulus premise is needed. The exact gcd is used in the original
modulus, without replacing the dominant seed by a normalized value.

Below the global bound, complete-pair exhaustion gives a base coefficient
V and overflow height H. Their charge is 4H and strict ordering gives H<=V.
The dominant period P=N/4 annihilates x_j. Since n=L_j+4, the gap becomes
16*K_j<=4*P+4*H, so

```
4*K_j <= P+V < 4*K_j+n.
```

The weight P+V represents the original target on the dominant axis alone.
Four binary boundaries cost eight coins, and the remaining tail is less
than n. The proved exponential estimate supplies that tail in at most
n/3-2 coins. This fits n, and the weight is large enough to refine to an
actual full-length rival. The window obstruction is generic in the
abelian group and arity; the direct cyclic consumer derives the complete
pair, gap, ordering and period from the original forest and its index.

The 72 new tests check explicit full-length rivals through n=67,68,128,256,
with actual small target relations, permutations and affine shifts. In
the extracted two-length-two-companion case, the even dominant index is
at most four and dyadic. The remaining case therefore has index TWO and
an even half modulus; the odd-half and index-four cases are now closed.
Other companion lengths, odd-axis/non-axis families, higher escapes and
unrestricted G1/G2/G3 remain OPEN. The global conjecture is not complete.

**Two length-two companions are closed in every even stratum (2026-09-08).**
`ChainForestProfileIndexTwo.lean` closes the remaining dominant-index-two
case and combines it with index four. The final theorem proves the sharp
GLOBAL bound for EVERY genuine even-axis forest with two length-two odd
companions at n>=67. It derives dominance, joint wide capacity, and the
possible subgroup indices internally. No numerical width, profile-family,
midpoint-phase, index, or seed-normalization premise is supplied by the
caller. An actual axis base and the stated forest/parity hypotheses remain
necessary; other profile families are not claimed closed.

For index two, the sum of the odd companion seeds lies in the dominant
subgroup. Choose 0<=z<M=N/2 so that z*x_j+x_a+x_k equals the original target.
With K=2^(L_j) and base coefficient V, the original forest relation gives

```
3*z = K+2*V-1+q*M,    q in {0,1,2}.
```

The complete-pair gap and strict ordering give 8K<=M+2V, while M<8K and
V<n. For q=1, the weight lies just above 3K and has a short tail. For q=0
or q=2, three times the weight lies within 2n of K or 17K. Splitting off
sixteen high binary positions fixes their coefficients at 21845 or 371370;
these have actual coin costs eight or eighteen. The lower tail costs at
most L_j-16, so adding ONE seed coin from EACH companion fits n=L_j+4.
The total weight is large enough to refine to an actual n-term rival.
All fixed arithmetic and representation witnesses are kernel checked.

The new tests construct full-length rivals through n=2048, with all odd
roots of the tested profile equations, nontrivial unit multiples,
coordinate permutations and affine shifts. They also check both fixed
binary windows at their error boundaries. The combined theorem removes
the entire two-length-two-companion even-axis branch in the established
large range. Remaining even-axis cases have at least one longer companion;
odd-axis/non-axis families, higher escapes, unrestricted G1/G2/G3 and the
global conjecture remain OPEN.

**Unequal companions sharpen the dominant index (2026-09-08).**
`ChainForestProfileUnequalIndex.lean` proves that an actual half-shaped
profile with unequal odd companion lengths cannot have the smaller full
companion width dividing the dominant gcd. Projecting the profile equation
through a divisor that kills the dominant seed and both companion widths
gives a zero sum of the two weighted HALF-widths. If the smaller full width
also vanished, the larger half-width would vanish while the smaller
half-width times an odd seed would remain nonzero. This is impossible.
The algebraic obstruction needs no tuple validity, axis base, genuine
endpoints or numerical cutoff once the actual half profile is supplied.

For a genuine subglobal even-axis forest in the established dominant
range, the family and dyadic index are extracted internally. With
unequal companion lengths L_a,L_k, the resulting gcd is 2^e with

```
1 <= e < min(L_a,L_k).
```

This strengthens the prior bound by the width of just one companion.
Together with the all-stratum closure for two length-two companions, it
forces gcd(N,x_j.val)=2 in EVERY remaining subglobal even-axis case with
a length-two companion at n>=67. The other companion is unrestricted
in that consumer; the supplied dominance is the one already extracted
from original three-escape data. This sharpens the residual structure,
but does not yet prove the global bound for the longer-companion cases.

The 167 new tests check the exact quotient equations across unequal
lengths and dyadic indices, with equal-length controls. A genuine valid
pair at N=520, lengths (4,2,2), and seeds (4,49,279) has index four;
permutations and affine shifts verify that the strict inequality cannot
be extended to equal lengths. The quotient checks are algebraic tests,
not claimed as validity certificates. Longer-companion charge bounds,
other profile families, unrestricted G1/G2/G3 and the global conjecture
remain OPEN.

**Uniform (2,3) companion arithmetic (2026-09-08).**
`ChainForestProfileTwoThreeArithmetic.lean` proves the coin representations
needed for both half-profile orientations with companion lengths two and
three. Write n=L+5, K=2^L, N/2=M=16K-d, and V=H+c-1<n. The hypotheses
include positive H,c, d+1<=4H, and the dyadic-height bound obtained from
H+7<n. For the bounded one-each-companion coefficient z, the short and
long overflow equations respectively lift to one of thirteen cases:

```
13z+qd+13 = (1+16q)K+12H+10c,
13z+qd+13 = (5+16q)K+ 8H+10c,    0 <= q < 13.
```

Except for short q=4 and long q=7, z has a fixed fifty-two-bit upper
prefix. Its greedy cost is at most 55; the arbitrary lower L-52 bits
and two companion coins therefore fit n. The proof checks every fixed
prefix in Lean and derives the error bounds uniformly for all n>=67.
It supplies actual binary representations, with coefficient at least n.
A generic binary-block/tail representation lemma and a congruence-lifting
lemma are also exported.

The integral cases use different companion weights. Short q=4 uses
weights (2,0) and Z=M+4V-c-3z, with K<=Z<K+2n. Long q=7 uses (2,2)
and Z=2z-V-M, with n<=Z<2K+n. Both have proved coin budgets. In particular,
the dense expansion immediately BELOW two widths still fits: its axis
cost is L+2, leaving room for the two companion coins. The 628 new tests
cover all thirteen residues in both orientations, actual n-term rivals,
unit multiples, permutations and affine shifts, and this dense boundary.
The relation fixtures are obstruction data, not valid-tuple certificates.

These arithmetic exports are now consumed by the genuine-forest
(2,3) global-bound theorem below. Longer companion pairs, other profile
families, unrestricted G1/G2/G3 and the global conjecture remain OPEN.

**Genuine (2,3) companion closure (2026-09-08).**
`ChainForestProfileTwoThree.lean` proves
`even_axis_two_three_companions_global_bound`: EVERY genuine even-axis
forest with one length-two and one length-three odd companion satisfies
the sharp GLOBAL bound at n>=67, in every even-modulus stratum. Its inputs
are the original forest, validity, genuine endpoints, companion lengths,
seed parities and an actual axis-base profile. It assumes no index,
dominance, wide-capacity, profile-family, midpoint or deficit certificate.

The proof derives n=L_j+5 and dominance, then uses the unequal-companion
index theorem to force index two in a hypothetical subglobal case.
The complete family consists of the axis base and one incompatible
overflow. The half-shape theorem gives the two companion orientations
(5,3) or (1,11), a dyadic height H, and a dyadic drop c. The charge is 8H;
subglobality forces H>1, allowing the midpoint theorem to force an ODD
half modulus M. With K=2^L_j and d=16K-M, the pair gap and this parity give
d+1<=4H. These are exactly the arithmetic hypotheses proved previously.

Index two produces a bounded coefficient for one coin on each companion
without normalizing the dominant seed. The two group equations derive
its thirteenths congruence. The twenty-four nonintegral cases and the two
alternative coefficients yield actual binary representations within the
original coin budget. Refinement gives an n-term rival whose short
companion weight differs from its top weight three, contradicting validity.
All steps are kernel checked; no external census premise is used.

The existing 628 obstruction tests cover every residue in both
orientations and full-length affine/permuted rivals. Another 36 controls
certify actual VALID genuine (2,3) pairs above the bound at n=24,67,68,
including the cutoff n=67. The certification exhausts all possible
n-coin companion weights and their unique feasible dominant lifts,
then checks the genuine endpoints and complete two-profile family.
Thus the closure excludes subglobal pairs while genuine pairs survive
above the bound. Remaining even-axis cases include (2,k) with k>=4
and pairs with both companions at least three. Other profile families,
higher escapes, unrestricted G1/G2/G3 and the global conjecture remain OPEN.

**Uniform (2,4) companion arithmetic (2026-09-08).**
`ChainForestProfileTwoFourArithmetic.lean` proves the complete coin
arithmetic for both half-profile orientations with companion lengths
two and four. With n=L+6, K=2^L, M=32K-d and V=H+c-1<n, the inputs
include H>=8 and d+1<=8H. The one-each coefficient has 27 phases in each
orientation. Fifty-two nonintegral phases select small companion weights
and fixed SIXTEEN-bit prefixes. Prefix plus companion cost is at most
22, so the remaining L-16 bits fit the original n-coin budget. The signed
coefficient formulas have a proved error below 200n; the lower binary
block dominates that error uniformly for all n>=67.

The integral short-overflow phase uses companion weights (12,0) when
c<=2H, with its coefficient just above two widths. For c>=2H it uses
(3,1), just above eight widths. The integral long-overflow phase uses
(2,2), below two widths plus a short tail. All signed formulas are proved
positive before conversion to natural weights, and every coin budget
has an actual binary representation. All finite choices are kernel
checked, with no external census assumption.

The 1,285 new regression cases cover every one of the 54 phases, both
short-overflow drop choices, actual full-length n-term rivals, unit
multiples, permutations and affine shifts. They include nonintegral
phases where the naive one-each rival is too expensive. These fixtures
satisfy the actual profile equations and are refuted by their rivals;
they are not presented as valid tuples. The genuine (2,4) forest theorem
below now derives and consumes these arithmetic inputs. Longer companion
pairs, other profile families, unrestricted G1/G2/G3 and the global
conjecture remain OPEN.

**Genuine (2,4) companion closure (2026-09-08).**
`ChainForestProfileTwoFour.lean` proves
`even_axis_two_four_companions_global_bound`: EVERY genuine even-axis
forest with one length-two and one length-four odd companion satisfies
the sharp GLOBAL bound at n>=67, in every even-modulus stratum. The
original forest data suffice; dominance, index, profile family, midpoint
parity, height and deficit conditions are all derived internally.

A hypothetical subglobal pair has dominant index two and a complete
axis-base/overflow family. Its charge is 16H. The dyadic half-shape and
subglobal charge force H>=8, so midpoint parity forces an odd half
modulus. With K=2^L_j and d=32K-M, the gap sharpens to d+1<=8H.
The actual cyclic equations yield all 27 phases in either orientation.
Signed group identities then evaluate the small companion choices and
the three integral-phase alternatives. Their proved positive coefficients
have actual binary representations, which refine to n terms. In every
case the long companion weight differs from its top weight fifteen,
so the resulting rival contradicts validity. No seed normalization or
external census premise is used.

The 1,285 earlier obstruction checks are supplemented by 36 genuine
VALID controls above the bound at n=24,67,68, with permutations and
affine shifts. Exhaustion of all possible n-coin companion weights and
their unique feasible dominant lifts certifies full multiset validity;
the endpoints and complete profile pair are also checked. The closure
therefore removes subglobal (2,4) pairs while genuine pairs survive
above the bound. Remaining even-axis cases include (2,k), k>=5, and
pairs with both companions at least three. Other profile families,
higher escapes, unrestricted G1/G2/G3 and the global conjecture remain OPEN.

**Equal length-three companion tools (2026-09-08).**
`ChainForestProfileThreeThreeAlgebra.lean` rules out the remaining
saturated corner by projection modulo sixteen. If the width, height and
drop are multiples of eight, an even axis and an odd overflow seed cannot
satisfy the top and half-profile equations at a modulus divisible by
sixteen. This obstruction uses no tuple validity or genuine endpoints.
The module also proves general dominant-gcd membership, extracts a
one-each companion coefficient at indices two, four and eight, and gives
a reusable signed coefficient identity for arbitrary companion relations.

`ChainForestProfileThreeThreeArithmetic.lean` proves all corresponding
coin budgets at n>=67. Eighteen nonintegral phases use sixteen-bit
prefixes; the three integral phases use four sparse alternatives. The
index-two low-drop alternative only needs the saturated corner excluded;
its integer granularity removes any need for a dyadic-drop hypothesis.
Every signed coefficient is proved positive and represented by actual
binary coins. The 543 new tests cover all 21 phases, full-length rivals,
unit multiples, permutations and shifts, plus exhaustive modulo-sixteen
checks and controls when each obstruction hypothesis is removed.

The genuine (3,3) theorem below now derives all arithmetic data and
consumes the corner obstruction internally. Longer companion pairs,
other profile families, unrestricted G1/G2/G3 and the global conjecture
remain OPEN.

**Genuine (3,3) and companion-sum-six closure (2026-09-08).**
`ChainForestProfileThreeThree.lean` proves the sharp GLOBAL bound for
EVERY genuine even-axis forest with two length-three odd companions
at n>=67, in every even-modulus stratum. Its original forest inputs
internally determine dominance, the complete profile pair, dyadic height
at least eight and the dominant index in {2,4,8}. The top equation gives
a bounded one-each coefficient at every index. All seven residue phases
then admit actual coin representations. The modulo-sixteen obstruction
excludes the saturated corner directly from the original equations;
no external corner, phase or arithmetic certificate is assumed.
Signed identities evaluate the alternatives, and refinement gives a
full-length rival distinguished on the second companion.

The combined theorem
`even_axis_companion_length_sum_le_six_global_bound` closes EVERY
genuine even-axis forest whose two positive companion lengths sum to
at most SIX, at n>=67. The family theorem excludes length-one arms in a
hypothetical subglobal case; the six ordered remaining pairs reduce to
the proved (2,2), (2,3), (2,4) and (3,3) cases. Width and wide capacity
are derived from the supplied length sum, so no dominance certificate
is required. Every remaining subglobal even-axis pair must therefore
have companion length sum at least seven.

The earlier 543 obstruction checks are supplemented by 108 genuine
VALID controls above the bound, at n=24,67,68 and each index two, four
and eight, including all permutations and affine shifts. Full validity
is certified by exhausting n-coin companion weights and unique feasible
dominant lifts; genuine endpoints and the complete profile pair are
also checked. The next length pairs are (2,5) and (3,4), alongside the
other profile families and axes. Higher escapes, unrestricted G1/G2/G3
and the global conjecture remain OPEN.

**Uniform companion algebra (2026-09-08).**
`ChainForestProfileCompanionAlgebra.lean` proves that every remaining
subglobal genuine even-axis forest with a supplied dominant-width
inequality has `1 <= e <= min(L_a,L_k)` and dominant gcd `2^e`.
Thus the actual index divides BOTH companion widths, including the
previously separate equal-length case. Projecting the top relation to
that quotient gives a bounded coefficient `z < N/gcd(N,x_j.val)` with
`z*x_j+x_a+x_k` equal to the distinguished sum. This is uniform in the
companion lengths and uses the original forest and axis-base data.

A second uniform obstruction treats widths `2s` and `2sr` with positive
`s,r` and even `r`. If the dominant width times its seed and the overflow
height times that seed vanish modulo `2s`, either half-profile orientation
with an odd short companion rules out `2s | N`. The profile drop cancels;
there is no divisibility assumption on it. A generic signed identity
combines the top and companion relations without normalizing any seed.

The regressions also produce actual full-length rivals for `(3,4)` at
indices two and four, both half-profile orientations and all 29 phases,
including both short integral alternatives. Fixed sixteen-bit prefixes
cost at most 17 coins together with the companions, against 23 available.
Permutations, unit scaling and translation are checked. This is
computational evidence is now supported by the uniform Lean arithmetic
below. The genuine `(3,4)` consumer is now closed below. `(2,5)`, other profile families,
unrestricted G1/G2/G3 and the global conjecture remain OPEN.

**Uniform (3,4) coin budgets (2026-09-08).**
`ChainForestProfileThreeFourArithmetic.lean` now proves the arithmetic
for every length `n >= 67`, both possible dominant indices two and four,
and both half-profile orientations. All 112 nonintegral phases have
kernel-checked signed choices with a fixed sixteen-bit prefix; the four
integral phases use six sparse alternatives. The short integral branch
splits at `2c <= 3H`, without requiring a dyadic drop or a corner exclusion.
Every signed coefficient is proved nonnegative and at least `n`, then
represented by actual dominant-chain coins within the full budget.

The uniform assumptions are `L+7=n`, `H>=4`, `c>0`, `V<n`, `H+c=V+1`,
`m+E=w*2^L`, `4E<=wH`, and the appropriate twenty-ninth phase equation,
where `w=64` or `32`. The genuine `(3,4)` theorem below now derives
these arithmetic data and consumes the signed identities and full-length
rivals internally. `(2,5)`, larger companion pairs, other profile families,
unrestricted G1/G2/G3 and the global conjecture remain OPEN.

**Genuine (3,4) closure (2026-09-08).**
`even_axis_three_four_companions_global_bound` proves the sharp global
bound for EVERY genuine even-axis forest with companion lengths three
and four at `n >= 67`, in every even stratum. The original forest supplies
all inputs: dominance and wide capacity, index two or four, the complete
axis-base/half-profile pair, height at least four, both half-profile
orientations, and all twenty-ninth phase equations. The uniform arithmetic
then yields actual full-length rivals. No index, normalization, midpoint,
residue, corner or coin-budget certificate is supplied externally.

The new valid-example controls exhaust all `n`-coin multisets for genuine
`(3,4)` forests at `n=24,67,68` and both indices above the bound. Their
complete profile family is `{(1,0,0),(0,11,7)}`; the only surviving full
multiset is the original all-ones tuple. Permutations and translations
preserve validity, distinct entries and every genuine endpoint.

Together with the companion-sum-six theorem, this leaves `(2,5)` as the
only unordered pair of companion sum seven in the even-axis branch.
Larger companion sums, other profile families and axes, unrestricted
G1/G2/G3 and the global conjecture remain OPEN.

**Uniform (2,5) coin budgets (2026-09-08).**
`ChainForestProfileTwoFiveArithmetic.lean` proves the fifty-fifth residue
arithmetic for every `n >= 67` at the forced dominant index two. The
short integral phase would force `5 | c`, which a dyadic profile drop
cannot satisfy. All 108 nonintegral phases have kernel-checked signed
choices with fixed sixteen-bit prefixes; two sparse alternatives cover
the long integral phase, split at `2c <= H`. The prefix and companions
cost at most 22 coins against 23 available. Every selected coefficient
is proved nonnegative and at least `n`, then represented by actual
binary coins within the original budget.

The hypotheses are `L+7=n`, `H>=4`, `c>0`, `V<n`, `H+c=V+1`,
`m+E=64*2^L`, `E<=16H`, and the appropriate phase equation. The long
integral alternatives need no dyadic or midpoint-parity assumption.
Regressions produce actual full-length rivals in all permitted phases,
including both integral alternatives, permutations, unit scaling and
translation; explicit controls check the divisibility obstruction.

The genuine `(2,5)` theorem below now derives these arithmetic data and
the short integral exclusion from the original forest. Larger companion
sums, other profile families and axes, unrestricted G1/G2/G3 and the
global conjecture remain OPEN.

**Genuine (2,5) and companion-sum-seven closure (2026-09-08).**
`even_axis_two_five_companions_global_bound` proves the sharp global
bound for EVERY genuine even-axis `(2,5)` forest at `n >= 67`, in every
even stratum. The original data give dominance, wide capacity, index
two, the complete profile pair, height at least four and both fifty-fifth
phase equations. The actual dyadic drop excludes the short integral
phase. A shifted representative handles the negative short leading
coefficient, and signed coin representations refine to full-length rivals.
No arithmetic or normalization certificate is supplied externally.

`even_axis_companion_length_sum_le_seven_global_bound` combines this
with all earlier cases. It proves the sharp global bound for every
positive companion length pair with sum at most SEVEN at `n >= 67`,
from original genuine even-axis forest and axis-base data alone. Width,
wide capacity and exclusion of length-one residual arms are internal.
Remaining subglobal even-axis pairs have companion sum at least eight.

The valid-example controls exhaust every `n`-coin multiset at
`n=24,67,68` above the bound. Their complete profile family is
`{(1,0,0),(0,5,15)}`, and their only surviving full multiset is the
original all-ones tuple. Permutations and translations preserve validity,
distinct entries and all genuine endpoints. The next unordered pairs are
`(2,6)`, `(3,5)` and `(4,4)`. Larger pairs, other profile families and axes,
unrestricted G1/G2/G3 and the global conjecture remain OPEN.

**Uniform equal-companion integral corner (2026-09-08).**
`ChainForestProfileEqualCorner.lean` classifies the saturated arithmetic
corner uniformly in the equal companion length. If an integral phase
has denominator `T` coprime to its height `H`, equal height and drop,
and saturated deficit `4E=wH`, projecting its phase equation modulo `T`
forces `T | 7`. For dyadic companion width and height, `T=2^a-1` and
`H=2^h`, so the only possible lengths are `a=1` or `a=3`.

Thus every equal companion length at least two other than three excludes
this saturated corner in an integral phase. Both exceptional lengths
have actual nonnegative phase controls; removing height coprimality,
integrality or saturation also has explicit counterexamples. This is a
uniform arithmetic classification, without a validity or seed premise.
It does not supply the remaining coin budgets or genuine-forest closure
for `(4,4)` or larger equal pairs. Those cases, the other sum-eight pairs,
other profile families and axes, unrestricted G1/G2/G3 and the global
conjecture remain OPEN.

**Complete axis basis and primitive phases (2026-09-08).**
`ChainForestProfileAxisBasis.lean` retains the actual dominant subgroup
index `D` in the rival construction. Besides the one-each coefficient
`z*x+a+b=V*x`, every companion has a bounded coefficient
`alpha*x=D*a`. A signed identity then evaluates every pair of nonnegative
companion weights `ta=tb+D*k`, with `k` an integer. When the companion is
a unit modulo `D`, this congruence is also necessary: it exactly
characterizes which pairs admit a bounded axis coefficient.

For equal companion half-width `s` and `D*F=2s`, the top and half-profile
relations give `(F*(2s-1)*alpha)*x=B*x`, where
`B+(s-1)*H=(s-1)*K+s*c`. This primitive relation retains phases lost by
restricting companion-weight differences to the full companion width.
The lemmas are group algebra and impose no normalization or validity
premise beyond their stated relations and index conditions.

The `(4,4)` probe now covers all 225 primitive index/residue cases and
produces actual full-length rivals, including permutations, unit scaling
and translations. The 210 nonintegral choices use 32-bit prefixes with
cost at most 30 against 40 available; the remaining 15 branches use
explicitly checked candidates. Two genuine-endpoint regression fixtures
show why the larger basis matters: a width-difference candidate costs
`n+1=68`, while index-congruent weights give a 9-coin representation that
refines to an actual 67-term rival. These tuples are invalid, as the
constructed rivals certify.

Uniform Lean coin budgets for the primitive phases and the genuine
`(4,4)` consumer remain OPEN. The other sum-eight pairs, larger companions,
other profile families and axes, unrestricted G1/G2/G3 and the global
conjecture remain OPEN.

**Uniform primitive `(4,4)` coin budgets (2026-09-08).**
`ChainForestProfileFourFourArithmetic.lean` proves actual full-length
representations for all 225 primitive phases at `n >= 67`, under the
index, period and phase equations. The 210 nonintegral phases use fixed
32-bit prefixes with uniform error below `2000*n`; the fifteen integral
phases use fixed sparse boundaries with tails below `3*n`. The resulting
signed coefficient is nonnegative and at least `n`, the total coin cost
is at most `n`, and the second companion differs from its original weight.
No additional dyadic, midpoint or saturated-corner premise is needed.

All eight exports are audited. Verification: 15,225 Lean build jobs,
4,070 standard-only or axiom-free declaration audits, and 17,106 forest
tests. The tests now use the fixed integral choices and include nondyadic
profiles and error boundaries. The genuine `(4,4)` consumer still needs
to derive the compatible primitive phases from the original forest.
The remaining companion-sum-eight closures, other families and axes,
unrestricted G1/G2/G3 and the global conjecture remain open.

**Genuine `(4,4)` closure (2026-09-08).**
`even_axis_two_length_four_companions_global_bound` in
`ChainForestProfileFourFour.lean` proves the sharp global bound for genuine
three-chain forests with an even axis base and two length-four companions,
for `n >= 67` in every even stratum. Original forest data determine all
four possible indices, the complete half-profile shape, both bounded
primitive phases and their compatibility congruence. The phase link uses
the actual half relation, including when the axis period shares factors
with fifteen. Both half-profile orientations give full-length rivals.
No extra width, index, phase, midpoint or coin-budget premise is supplied
by the caller.

Verification: six new audited exports, 15,226 Lean build jobs, 4,076
standard-only or axiom-free declaration audits, and 17,110 forest tests.
The phase controls explicitly reject cancellation of fifteen without the
actual half relation. Companion sums at most seven were already closed;
only `(2,6)` and `(3,5)` remain among unordered companion-sum-eight pairs.
Larger pairs, other families and axes, unrestricted G1/G2/G3 and the
unrestricted global conjecture remain open.

**Uniform primitive `(2,6)` coin budgets (2026-09-08).**
`ChainForestProfileTwoSixArithmetic.lean` proves actual full-length
representations for all 222 primitive phases of the two half-profile
orientations at `n >= 67`, under their compatible phase equations.
Fixed 32-bit prefixes handle 220 nonintegral phases; the two integral
phases each use one dominant width plus a short nonnegative tail.
The signed coefficient is nonnegative and at least `n`, the second
companion differs from its original weight, and total coin cost is
at most `n`. No extra dyadic or midpoint hypothesis is needed.

Verification: six new audited exports, 15,227 Lean build jobs, 4,082
standard-only or axiom-free declaration audits, and 19,997 forest tests.
The 2,887 new tests include actual full-length rivals across all 222
phases with all six coordinate orders and affine changes, plus nondyadic
profiles and error boundaries. The full phase coverage uses dimensions
67, 108 and 128. Deriving these primitive equations from the original
`(2,6)` forest remains the next consumer step. The genuine `(4,4)` class
and companion sums at most seven are closed; the genuine `(2,6)` and
`(3,5)` consumers, larger pairs, other families and axes, unrestricted
G1/G2/G3 and the global conjecture remain open.

**Genuine `(2,6)` closure (2026-09-08).**
`even_axis_two_six_companions_global_bound` in
`ChainForestProfileTwoSix.lean` proves the sharp global bound for genuine
three-chain forests with an even axis base and companion lengths two and
six, for `n >= 67` in every even stratum. The original forest determines
index two, both half-profile orientations, the bounded primitive phases
and their compatibility. Both period shifts are handled explicitly;
the link uses the actual half relation without assuming coprimality to
111. Affordable representations refine to actual full-length rivals.
The caller supplies no additional index, width, phase or budget premise.

Verification: five new audited exports, 15,228 Lean build jobs, 4,087
standard-only or axiom-free declaration audits, and 19,999 forest tests.
The tests include controls showing that the scalar equations and top
relation alone do not imply the phase link. Together with the established
`(4,4)` closure and all companion sums at most seven, this leaves only
`(3,5)` among unordered companion-sum-eight pairs. Larger pairs, other
families and axes, unrestricted G1/G2/G3 and the global conjecture remain
open.

**Uniform primitive `(3,5)` coin budgets (2026-09-08).**
`ChainForestProfileThreeFiveArithmetic.lean` proves actual full-length
representations for all 354 primitive phases at `n >= 67`, under the
compatible phase equations for both indices and half-profile orientations.
Fixed 32-bit prefixes cover 348 nonintegral phases; six fixed sparse
boundaries cover the integral cases. Each signed coefficient is
nonnegative and at least `n`, the second companion differs from its
original weight, and total coin cost is at most `n`. No additional
dyadic, midpoint or saturated-corner hypothesis is needed.

Verification: ten new audited exports, 15,229 Lean build jobs, 4,097
standard-only or axiom-free declaration audits, and 24,602 forest tests.
The 4,603 new tests cover actual full-length rivals across every phase,
all coordinate permutations and affine changes, plus nondyadic profiles
and error boundaries. Deriving these phase equations from the genuine
`(3,5)` forest is the next consumer step. This is the last unordered
companion-sum-eight pair; its genuine closure, larger pairs, other
families and axes, unrestricted G1/G2/G3 and the conjecture remain open.

**Companion length sum at most eight closed (2026-09-08).**
`even_axis_three_five_companions_global_bound` in
`ChainForestProfileThreeFive.lean` closes the genuine even-axis `(3,5)`
class for `n >= 67` in every even stratum. Both possible indices,
half-profile orientations and compatible primitive phases are derived
from the original forest and actual axis-base data. Actual affordable
representations refine to full-length rivals.

`even_axis_companion_length_sum_le_eight_global_bound` now combines
all established cases and proves the sharp global bound whenever the two
positive companion lengths sum to at most eight. The caller supplies no
extra dominance, index, phase or coin-budget premise; length-one arms
are also handled internally.

Verification: six new audited exports, 15,230 Lean build jobs, 4,103
standard-only or axiom-free declaration audits, and 24,674 forest tests.
The 72 additional checks certify genuine valid forests above the bound
at both indices, with every possible n-coin multiset checked through its
bounded companion weights. Larger companion sums remain open; the next
unordered pairs are `(2,7)`, `(3,6)` and `(4,5)`. General primitive relations
and uniform budgets for larger widths, other profile families and axes,
unrestricted G1/G2/G3 and the global conjecture remain open.

**Uniform unequal-companion primitive algebra (2026-09-08).**
`ChainForestProfileUnequalBasis.lean` proves the primitive and one-each
signed relations for both half-profile orientations at arbitrary widths
`2*s`, `2*t`, with `t=s*u`, `D*F=s` and `T+u+1=4*t`. Binary unequal
companion widths are a specialization. Combining the original top and
half relations gives the full phase coupling `T | 4*r+q`, even for signed
phases. This needs no coprimality assumption on a companion weight, phase
denominator or actual axis period.

Verification: six new audited exports, 15,231 Lean build jobs, 4,109
standard-only or axiom-free declaration audits, and 26,945 forest tests.
The 2,271 new checks use actual cyclic-group relations with arbitrary
ratios, nonbinary widths, signed phases and shared factors. Controls
show that removing the top relation can preserve the weighted half-phase
congruence while breaking the full link.

All genuine even-axis companion length sums at most eight remain closed
at `n >= 67`. These uniform identities remove repeated pair-specific
algebra; larger coin budgets, other profile families and axes,
unrestricted G1/G2/G3 and the global conjecture remain open.

**Uniform bounded unequal-companion phases (2026-09-08).**
`ChainForestProfileUnequalPhases.lean` derives bounded primitive phases
from actual top and half-profile relations, the actual axis index, the
dominant width and the forest gap. A general signed-target lemma replaces
manual period shifts. The gap implies `M >= 3*t*K`, and all four target
coefficients lie strictly between `-M` and `M`.

For widths `2*s`, `2*t`, ratio `u >= 2`, `D*F=s` and
`T+u+1=4*t`, short profiles give `0 <= r < F*T`; long profiles give
`1 <= r <= F*T`. The one-each phase has `0 <= q <= T`; positive targets
exclude `q=T`, and negative targets exclude `q=0`. In the short orientation
the target is positive for `u <= 3` and negative for `u >= 4`; the long
one-each target is positive. Both consumers derive the full link
`T | 4*r+q`, with no supplied phases or coprimality assumptions.

Verification: five new audited exports, 15,232 Lean build jobs, 4,114
standard-only or axiom-free declaration audits, and 27,219 forest tests.
The 274 new tests cover 21,782 actual group-and-gap fixtures, both phase
endpoints, shared factors, nonbinary widths and general signed-target
windows, with controls for missing window or canonical-coefficient bounds.

All genuine even-axis companion length sums at most eight remain closed
at `n >= 67`. Consume this uniform phase extraction in arbitrary-length
genuine forests and extend the actual coin budgets. Larger companion
sums, other profile families and axes, unrestricted G1/G2/G3 and the
global conjecture remain open.

**Uniform genuine unequal-companion reduction (2026-09-08).**
`ChainForestProfileUnequalForest.lean` connects the bounded primitive
algebra to every ordered unequal companion length pair. Original
genuine forest data and the actual even-axis profile supply the actual
index `D=2^e`, with `1 <= e < L_a`, dyadic height `H` and drop `c`, both
basis coefficients, the bounded natural phases and the full phase link.
The data retain the original top and half relations, `H+c=V+1 <= n`,
the gap and its strictly excessive charge.

The profile orientation also retains its actual coin cost:
`H+3*s+t <= n+2` for the short half or `H+s+3*t <= n+2` for the long
half. At `n >= 24` the reduction accepts the standard dominant-width
hypothesis. At `n >= 67`, a maximal axis derives that threshold internally
from validity and genuineness, so no numerical dominance or phase input
is required. Companion lengths are arbitrary; this is a structural
reduction, not a proof of their remaining uniform coin budgets.

Verification: five new audited declarations, including the primitive-data
definition, 15,233 Lean build jobs, 4,119 standard-only or axiom-free
declaration audits, and 28,180 forest tests. The 961 new tests exercise
80 actual genuine-chain obstruction cases, both orientations and indices
through sixteen, under permutations and affine changes. Every case has
an explicit full-size rival, refuting its validity; the fixtures do not
assume validity or certify a uniform budget theorem.

All genuine even-axis companion sums at most eight remain closed at
`n >= 67`. Larger uniform coin budgets, other profile families and axes,
unrestricted G1/G2/G3 and the global conjecture remain open.

**Uniform signed-rival arithmetic (2026-09-08).**
`ChainForestProfileUnequalRival.lean` reduces the two compatible basis
coefficients to one primitive coefficient and an exact period multiple.
In the short orientation `4*F*alpha+z=K+2*c-1+p*M`; in the long
orientation it equals `-3*K+4*H+2*c-1+p*M`, where `T*p=4*r+q`.

Every signed rival `Z=tb*z-kappa*alpha+(1-tb)*V-nu*M` now has a
uniform exact error formula `F*T*Z-R*K=A*H+B*c-F*T+J*E`, with
`M+E=4*F*t*K`. Both orientations have explicit coefficients. A general
certificate turns bounds on `A`, `B` and `J` into a strict linear window
throughout `H+c <= n` and `E <= W*H`. This separates the common scalar
arithmetic from the remaining choice of affordable coins.

Verification: five new audited exports, 15,234 Lean build jobs, 4,124
standard-only or axiom-free declaration audits, and 28,473 forest tests.
The 293 new tests check the exact formulas on actual larger-width group
data, several signed rival choices, whole height/drop/deficit regions,
and controls for the positive-height, denominator and gap hypotheses.

Uniform binary-prefix budgets and coin choices for larger widths remain
open, as do other profile families and axes and unrestricted G1/G2/G3.
All genuine even-axis companion sums through eight remain closed at
`n >= 67`; the global conjecture is not yet proved.

**Arbitrary binary-prefix representation budgets (2026-09-08).**
`ChainForestProfileBinaryPrefix.lean` removes the fixed 32-bit prefix,
eight companion positions and `2000*n` error from the representation
helper. For `L=e+(w+1)`, a nonintegral rational window with error below
`2^e` fixes the exact prefix. Its explicit cost plus the tail and companion
cost gives an actual `L`-coin representation, including nonnegativity
and a coefficient at least `n`. Prefix and tail lengths, denominator,
error allowance and companion budget are parameters.

A third theorem consumes the uniform signed-rival coefficient certificate
directly, producing the actual representation once its prefix budget and
tail-size conditions hold. This connects the common error arithmetic to
coin representations for arbitrary companion length sums; selecting
suitable rival coins and proving their budgets uniformly remains open.

Verification: three new audited exports, 15,235 Lean build jobs, 4,127
standard-only or axiom-free declaration audits, and 28,723 forest tests.
The 250 new tests exercise prefixes from two to forty bits, varied tails,
companion-length sums including nine, thirteen and twenty-five, exact
coin representations and boundary controls for the window hypotheses.
All genuine even-axis companion sums through eight remain closed at
`n >= 67`. Larger uniform coin choices, other families and axes, and the
unrestricted global conjecture remain open.

**Complementary rival representation budgets (2026-09-08).**
`ChainForestProfileComplementary.lean` proves exact combined greedy costs
for complementary binary blocks. When two positive rational numerators
sum to `m*T` and their prefixes are nonintegral, the prefix costs add to
`2*m+bits-2`. Bounds on the two companions' combined weights then ensure
that one prefix pays for both companions and its tail whenever
`6*m <= bits+6`.

The final theorem consumes both signed rational windows and produces an
actual affordable representation for at least one coefficient, without
assuming either individual prefix-popcount budget. Constructing suitable
complementary pairs uniformly is the next obligation. Integral prefixes
remain a separate case; omitting nonintegrality can make both budgets fail.

Verification: seven new audited exports, 15,236 Lean build jobs, 4,134
standard-only or axiom-free declaration audits, and 29,204 forest tests.
The 481 new tests cover exact complementary costs, combined companion
weights, actual representations for one of two windows, and controls for
the top-multiple and nonintegrality assumptions.

All genuine even-axis companion sums through eight remain closed at
`n >= 67`. Larger uniform rival selection, integral phases, other profile
families and axes, and unrestricted G1/G2/G3 remain open; the global
conjecture is not yet proved.

**Actual complementary construction and bounded approximation (2026-09-08).**
`ChainForestProfileComplementaryConstruction.lean` proves that a signed
primitive multiple, shifted by the top relation, evaluates to the actual
target with nonnegative companion weights. Both signs share one exact
height/drop/deficit error formula. A cancellation identity bounds the
deficit coefficient using the leading error, avoiding a large raw phase
bound.

An integer form of Dirichlet approximation supplies a positive bounded
multiple and a signed period multiple. It deliberately makes no
nonintegrality claim: an approximation can become integral even when the
original fraction is not. A sharper complementary-budget consumer uses
the exact combined companion cost and produces an actual representation
without assuming either individual prefix budget.

Verification: six new audited exports, 15,237 Lean build jobs, 4,140
standard-only or axiom-free declaration audits, and 29,473 forest tests.
The 269 new tests check actual cyclic-group rivals and their errors,
signed integer approximations, the integral-approximation control, and
representations beyond the earlier crude top-multiple bound.

Uniform geometric bounds, integral boundaries, and the remaining profile
families and axes still need proof. All genuine even-axis companion sums
through eight remain closed at `n >= 67`; unrestricted G1/G2/G3 and the
global conjecture remain open.

**Integral-phase obstruction and sparse-tail certificates (2026-09-08).**
`ChainForestProfileIntegralCertificates.lean` derives a coprimality
restriction from the actual integral primitive equation when widths and
drop are dyadic. It imposes no coprimality assumption on the axis period.
A general coefficient cone bounds the rival error above minus one
denominator. At an integral boundary, integer granularity then forces a
nonnegative tail. An arbitrary sparse binary block and bounded tail give
an actual representation, with explicit length and companion-cost budgets.

Verification: five new audited exports, 15,238 Lean build jobs, 4,145
standard-only or axiom-free declaration audits, and 29,761 forest tests.
The 288 new tests cover the coprimality obstruction, overlapping binary
blocks, actual sparse representations, and the strict-positivity boundary.
No placeholders or extra axioms are used.

The certificates are conditional on choosing suitable rival coefficients;
uniform selection still needs proof. A separate search found candidates
for all 854 primitive phases of companion lengths `(4,5)`, including all
14 integral phases. This is computational evidence awaiting Lean
verification, not a new closed family. All genuine even-axis companion
sums through eight remain closed at `n >= 67`; unrestricted G1/G2/G3 and
the global conjecture remain open.

**Complete four-five primitive arithmetic (2026-09-08).**
`ChainForestProfileFourFiveArithmetic.lean` checks all 854 primitive
phases at the three possible indices. The 840 nonintegral phases have
complementary top-shift certificates; the fourteen integral phases have
sparse-boundary certificates with positive error cones. Finite checks use
Lean kernel reduction. A unified consumer produces an actual group rival
and an affordable full-length coin representation for every `n >= 67`.
Either companion may distinguish the rival from the original tuple.

Verification: six new audited exports, 15,239 Lean build jobs, 4,151
standard-only or axiom-free declaration audits, and 32,325 forest tests.
The 2,564 new tests include actual cyclic-group instances and complete
coin representations for every phase at three lengths, complete phase
coverage, and the first-companion distinction required by a top shift.
No placeholders, extra axioms or `native_decide` are used.

The candidate search is now replaced by a complete arithmetic proof.
The next step is to supply its inputs from the original genuine forest
and derive the sharp `(4,5)` bound. That forest family is not yet claimed
closed at this checkpoint. All positive companion sums through eight
remain closed at `n >= 67`; unrestricted G1/G2/G3 and the conjecture
remain open.

**Genuine four-five forest closure (2026-09-08).**
`ChainForestProfileFourFive.lean` proves the sharp global bound for
original genuine even-axis forests with companion lengths `(4,5)` for
every `n >= 67`, in every even stratum. The shared unequal-companion
reduction derives the index, dyadic height and drop, gap, and compatible
primitive phases internally. The complete arithmetic then gives an
actual affordable rival; joint refinement preserves a distinction on
either companion and contradicts tuple validity. No phase, numerical
dominance or extra coin-budget premises remain in the forest theorem.

Verification: three new audited exports, 15,240 Lean build jobs, 4,154
standard-only or axiom-free declaration audits, and 33,180 forest tests.
The 855 new tests refine every primitive phase to a full-length tuple
rival under all chain permutations and affine changes, and check the
first-companion distinction. No placeholders or extra axioms are used.

All positive companion sums through eight and the sum-nine pair `(4,5)`
are now closed in this genuine even-axis class. The remaining sum-nine
pairs are `(2,7)` and `(3,6)`. A new complete search finds candidates for
all 714 phases of `(3,6)`, using variable prefix widths and each
orientation's original cost threshold; those candidates still need Lean
verification. The current complementary search misses 108 short phases
of `(2,7)`, which is not a counterexample. Larger uniform selection,
other profile families and axes, unrestricted G1/G2/G3, and the global
conjecture remain open.

**Complete three-six primitive arithmetic (2026-09-08).**
`ChainForestProfileThreeSixArithmetic.lean` checks all 714 primitive
phases: 708 complementary pairs with individually certified prefix widths
and error constants, plus six integral sparse boundaries. A general
base-length lemma propagates each error bound to every larger length.
The short orientation starts at 67 and the long at its original cost
threshold 99. The unified consumer produces actual affordable group
rivals and full-length coin representations. The positive short-phase
endpoint is retained, and no coprimality of the period with 119 is assumed.

Verification: seven new audited exports, 15,241 Lean build jobs, 4,161
standard-only or axiom-free declaration audits, and 35,324 forest tests.
The 2,144 new tests instantiate every phase at three lengths and check
actual cyclic-group rivals, complete coin representations, coverage,
integral boundaries and the first-companion distinction. The finite
certificates use kernel reduction; no placeholders or extra axioms occur.

The next step is to derive the orientation threshold and all inputs from
the original genuine forest, closing `(3,6)` at `n >= 67`. That forest
closure is not yet claimed here. The verified even-axis frontier remains
all positive companion sums through eight and the pair `(4,5)`. The
remaining `(2,7)` work and all unrestricted global gates remain open.

**Genuine three-six forest closure (2026-09-08).**
`ChainForestProfileThreeSix.lean` proves the sharp global bound for
original genuine even-axis forests with companion lengths `(3,6)` for
every `n >= 67`, in every even stratum. The original long half-profile
cost forces `n >= 99` internally, so the complete arithmetic covers both
orientations without an additional length premise. The shared forest
reduction supplies all index, dyadic, gap and phase data, and joint
refinement produces an actual full-length rival contradicting validity.

Verification: two new audited exports, 15,242 Lean build jobs, 4,163
standard-only or axiom-free declaration audits, and 36,039 forest tests.
The 715 new tests cover every phase under affine changes and all chain
permutations, checking actual full-tuple collisions after joint coin
refinement. No placeholders or extra axioms are used.

All positive companion sums through eight and the sum-nine pairs `(4,5)`
and `(3,6)` are now closed in this genuine even-axis class. Only `(2,7)`
remains at sum nine; the next attempt uses the full signed primitive
basis to address phases missed by the complementary top-shift search.
Larger uniform selection, other profiles and axes, unrestricted G1/G2/G3,
and the global conjecture remain open.

**Complete two-seven primitive arithmetic (2026-09-08).**
`ChainForestProfileTwoSevenArithmetic.lean` checks all 446 primitive
phases. The full signed primitive basis supplies individually affordable
rivals for all 444 nonintegral phases, including those missed by the
complementary top-shift search. The two integral phases use positive
sparse-boundary certificates. The unified consumer produces actual group
rivals and full-length coin representations for every `n >= 67`, retaining
the exact second-phase endpoint and link.

Verification: five new audited exports, 15,243 Lean build jobs, 4,168
standard-only or axiom-free declaration audits, and 37,378 forest tests.
The 1,339 new tests instantiate every phase at three lengths, checking
actual group evaluations, complete representations, integral boundaries
and phase coverage. The finite certificates use kernel reduction; no
placeholders or extra axioms occur.

All sum-nine pairs now have complete arithmetic, but the original
`(2,7)` genuine-forest consumer and the combined sum-nine closure are
still being checked. The verified forest frontier remains all positive
companion sums through eight, plus `(4,5)` and `(3,6)`. Larger uniform
selection, other profiles and axes, unrestricted G1/G2/G3 and the global
conjecture remain open.

**Complete genuine even-axis companion sums through nine (2026-09-08).**
`ChainForestProfileTwoSeven.lean` closes the original genuine `(2,7)`
even-axis forest bound and combines all established cases in
`even_axis_companion_length_sum_le_nine_global_bound`. Every positive
companion-length sum at most nine is now covered at `n >= 67`, in every
even stratum, including both orders of `(2,7)`, `(3,6)` and `(4,5)` and
the previously established short-arm cases. The original forest and its
actual axis profile derive every index, dyadic, phase and coin input;
no numerical dominance or extra budget premises remain.

Verification: three new audited exports, 15,244 Lean build jobs, 4,171
standard-only or axiom-free declaration audits, and 37,825 forest tests.
The 447 new tests refine every two-seven phase to a full-length tuple
rival under all chain permutations and affine changes, and check the
first-companion distinction. No placeholders, extra axioms or
`native_decide` are used.

The sum-nine frontier is closed in this genuine even-axis class. The
next work is uniform larger companion selection using the full primitive
basis and the shared error/representation certificates. The new sum-ten
pairs are `(2,8)`, `(3,7)`, `(4,6)` and `(5,5)`; none is claimed closed
here. Other profile families and axes, unrestricted G1/G2/G3, and the
global conjecture remain open.

**Uniform basis certificates and genuine unequal sum-ten pairs (2026-09-08).**
`ChainForestProfileBasisCertificates.lean` supplies a shared signed-basis
error identity, nonintegral-prefix and integral-boundary consumers for
arbitrary companion lengths, and exact normalization of compatible phases.
`ChainForestProfileSumTenArithmetic.lean` uses this layer to kernel-check
all 4,050 phases of `(2,8)`, `(3,7)` and `(4,6)`, including all 22 integral
phases. Every certificate gives an actual affordable group rival for
all `n >= 67`.

`ChainForestProfileSumTen.lean` derives every required index, phase and
period-deficit input from the original genuine even-axis forest.
`even_axis_sum_ten_unequal_companions_global_bound` proves the sharp global
bound for these three ordered unequal pairs in every even stratum, with
no extra numerical dominance, phase or coin premises. Swapping the two
companion labels covers the reverse orders.

Verification: nine new audited exports, 15,247 Lean build jobs, 4,180
standard-only or axiom-free declaration audits, and 54,026 forest tests.
The 16,201 new tests cover every phase at three lengths and refine every
phase to a full-length tuple collision under all chain permutations and
affine changes. No placeholders, extra axioms or `native_decide` are used.

Every positive companion sum through nine remains closed. The equal pair
`(5,5)` is the remaining sum-ten case; the shared certificate layer is
available for that case and for uniform larger-companion work. Other
profile families and axes, unrestricted G1/G2/G3, and the global conjecture
remain open.

**General equal-phase certificates and genuine companion sums through ten (2026-09-08).**
`ChainForestProfileEqualBasisCertificates.lean` proves compatible bounded
primitive phases for arbitrary equal companion widths, using the actual
top and half relations without assuming that the axis period is coprime
to the primitive denominator. Its new general certificate consumer handles
rivals just below an integral binary boundary: the preceding prefix and
the entire lower block are charged to the representation budget.

`ChainForestProfileFiveFiveArithmetic.lean` kernel-checks all 961 equal-five
phases. There are 897 nonintegral certificates, 31 positive integral
certificates and 33 certificates below integral boundaries. All give
actual affordable group rivals for every `n >= 67`, with no extra dyadic
or starting-length requirements.

`ChainForestProfileFiveFive.lean` derives those arithmetic inputs from the
original genuine even-axis forest and proves the `(5,5)` bound in every
even stratum. Its `even_axis_companion_length_sum_le_ten_global_bound`
combines the established pairs to cover every positive companion-length
sum at most ten. No extra dominance, phase or coin premises remain.

Verification: eight new audited exports, 15,250 Lean build jobs, 4,188
standard-only or axiom-free declaration audits, and 57,871 forest tests.
The 3,845 new tests instantiate every equal-five phase at three lengths
and refine every phase under all chain permutations and affine changes.
No placeholders, extra axioms or `native_decide` are used.

The next work is uniform larger-companion selection. The new boundary
certificates suggest a construction for even primitive phases of equal
companions at arbitrary lengths; this is a next proof obligation, not
a completed uniform closure. Other profile families and axes,
unrestricted G1/G2/G3, and the global conjecture remain open. Continue
through verified milestones and commit and push each to both repositories.

**Uniform even primitive phases for arbitrary equal companions (2026-09-08).**
`ChainForestProfileEqualEven.lean` supplies an explicit rival for equal
companion lengths `a = k+2` with no upper bound on `a`. Below the maximal
index, write the primitive factor as `2*G` and the index relation as
`D*G = 2^(a-1)`. Every compatible even primitive phase has companion
weights `3*2^(a-2)-1` and `5*2^(a-2)-1`, with combined coin cost `2*a-1`.
The exact axis coefficient satisfies `2*Z = 3*2^L-H-2`; the drop and
period terms cancel. The ordinary width bound `2*n <= 2^L` gives a
full-length representation with total cost at most `n`.

`odd_primitive_phase_of_valid_equal_companion_forest` consumes the rival
in an actual valid chain forest and forces its compatible primitive phase
to be odd. This is a uniform residual reduction at every equal companion
length, using actual primitive basis/phase data and the axis width bound.
It does not yet derive all those phase inputs from an arbitrary original
genuine forest, or eliminate the remaining odd phases or maximal index.

Verification: five new audited exports, 15,251 Lean build jobs, 4,193
standard-only or axiom-free declaration audits, and 60,212 forest tests.
The 2,341 new tests construct actual groups across equal lengths two
through forty and every nonmaximal index, verify the exact axis
coefficient, and refine full tuple rivals under permutations and affine
changes. No finite certificate table, fixed prefix width, placeholders,
extra axioms or `native_decide` are used in the uniform proof.

The genuine companion-sum-through-ten bound remains proved. Next derive
the uniform phase reduction directly from genuine forest data and address
the remaining odd phases and maximal indices. Other profile families and
axes, unrestricted G1/G2/G3, and the global conjecture remain open.
Continue through milestones and commit and push each verified milestone
to both repositories.

**Uniform primitive reduction from genuine equal-companion forests (2026-09-08).**
`ChainForestProfileEqualForest.lean` derives complete reduced primitive
data from an original subglobal genuine forest with a maximal even axis
and arbitrary equal companion lengths, for every `n >= 67` and every
even stratum. The forest supplies the index exponent, dyadic height and
drop, original half-profile cost, gap, strict charge, actual bounded
coefficients and compatible phases in either overflow orientation.

`EqualCompanionReducedPrimitiveData` retains the alternative `F=1` or an
odd primitive phase. Here `F=1` is the maximal companion index; every
smaller index has odd phase because the uniform even-phase rival would
contradict validity. No phase, coin-budget or extra numerical dominance
premises are supplied to the genuine-forest theorem. The maximal-axis
hypothesis remains explicit.

A new general estimate obtains the bounded phases from only the ordinary
width `2*n <= K` and equal-companion gap. It does not require the earlier
large numerical threshold or coprimality between the axis period and
primitive denominator.

Verification: four new audited exports, 15,252 Lean build jobs, 4,197
standard-only or axiom-free declaration audits, and 61,935 forest tests.
The 1,723 new tests construct actual cyclic-group phases exactly at
`K=2*n`, for widths through 1,024, including periods sharing the full
primitive denominator. No placeholders, extra axioms or `native_decide`
are used.

The original equal-companion residual is now maximal index or odd phase
at every companion length. Eliminating those cases, arbitrary larger
unequal companions, other profile families and axes, unrestricted
G1/G2/G3, and the global conjecture remain open. The genuine companion
sum-through-ten bound remains proved. Continue after each milestone,
committing and pushing verified work to both repositories.

**Odd equal phases determine the truncated modulus stratum (2026-09-08).**
`ChainForestProfileEqualStratum.lean` connects the genuine equal-companion
height `H=2^h` to the actual modulus. For companion length `a` and
nonmaximal index `2^e`, every `t <= a-e` satisfies
`2^(e+t) | N` if and only if `t <= h`. This follows from the primitive
factor dividing `H+r*M` and the internally derived oddness of `r`.

When `h < a-e`, the exact modulus stratum is `N=2^(e+h)*q` with `q` odd.
When `h >= a-e`, the conclusion is `2^a | N`; no exact valuation beyond
that cutoff is claimed. The original genuine-forest theorem derives the
profile together with all prior reduced phase data, retaining the
maximal-index alternative and the explicit maximal-axis hypothesis.

Verification: six new audited exports, 15,253 Lean build jobs, 4,203
standard-only or axiom-free declaration audits, and 62,371 forest tests.
The 436 new tests construct actual odd primitive phases with exact and
truncated period valuations and verify every relevant dyadic divisibility
test, both scalar equations and the original top and half group relations.
No placeholders, extra axioms or `native_decide` are used.

The genuine companion-sum-through-ten bound remains proved. Odd phases
and maximal indices have not been eliminated; the new result restricts
their possible strata. Larger unequal companions, other profile families
and axes, unrestricted G1/G2/G3, and the global conjecture remain open.
Continue after verified milestones, committing and pushing both
repositories.

**2026-09-08 — maximal-index equal companions satisfy the global bound at arbitrary lengths.**
`ChainForestProfileEqualMaximalArithmetic.lean` and
`ChainForestProfileEqualMaximal.lean` close the entire maximal-index branch
of the genuine maximal-even-axis equal-companion class at `n >= 67`, in
every even modulus stratum. The companion length `a` is unrestricted.
The genuine theorem derives all period and phase data internally from the
forest, its actual index `2^a`, top/half profiles, and gap.

Write `T=2^a-1`, `K=2^L`, `M+E=(T+1)K`, and
`E <= 2^(a-2)H`. Equal companion weights `t` give the exact identity
`T Z-(t+(T+1)j)K=(T-t)(H+c)-T-jE` when `tq=T nu+j`.
For `q != T-1`, a common divisor gives an annihilator with `j=0`,
or a modular inverse gives `j=1` and `t<T-1`. The variable `a`-bit
prefix and both companions cost at most `3a`. Actual half-profile cost
implies `12a<=n` and `2Tn<2^(n-3a)`, so the full axis tail is affordable.
For `q=T-1`, `t=T-1` gives an integral boundary at `2K`. Below it,
three upper coins plus the full lower block meet the budget exactly;
at or above it, four upper coins plus a short binary tail suffice.
Every branch produces an actual distinct full-length tuple rival.

The new genuine residual theorem has **strictly smaller index** `e<a`,
retains all reduced primitive data (whose phases are therefore odd), and
proves `2^(e+t)|N iff t<=h` for every `t<=a-e`. The maximal-axis hypothesis
remains explicit. Smaller-index odd phases, unrestricted G1/G2/G3, and
the unrestricted conjecture remain open.

Verification: 11 new theorem exports; full Lean build **15,255 jobs**;
axiom audit **4,214 declarations** (4,211 standard-only and three
axiom-free); full forest suite **70,624 passed**. The 8,253 new regressions
cover all modular phases through companion length 12, selected widths
through 128, and actual cyclic-group tuple collisions through length 12
with both multiplier branches, all integral error signs, odd companions,
dyadic height/drop, every coordinate order, and an affine transform.

**2026-09-08 — every remaining equal-companion phase is a unit.**
`ChainForestProfileEqualCoprime.lean` excludes noncoprime one-each phases
uniformly at every equal-companion index. With `T=2^a-1`, a nontrivial
`gcd(q,T)` supplies `1<=t<T` and `tq=T*nu`. The equal-weight rival has
`T Z=tK+(T-t)(H+c)-T`: the period cancels completely. The actual
half-profile cost gives `2Tn<K`, placing `n<=Z<K`. Its complete axis and
companion representations use at most `n-2` coins and refine to a distinct
size-`n` tuple collision.

The original genuine maximal-even-axis forest now supplies strictly
smaller index `e<a` and `EqualCompanionOddCoprimePrimitiveData`: all bounded
basis coefficients and phases, odd `r`, `Coprime q T`, both scalar and
group relations, the actual half-profile cost, gap, charge, dyadic height
and drop, and the modulus profile through companion width. No phase or
period coprimality premise is supplied. Moreover, `T | 2r+q` and odd `r`
imply `Coprime r (2^(a-e)*T)`, so the primitive phase is a unit modulo its
entire denominator.

Verification: six new audited theorem exports, full Lean build **15,256
jobs**, **4,220** standard-only or axiom-free declaration audits, and
**70,743** forest tests. The 119 new regressions cover every smaller index
through equal companion length 12, both zero and nonzero nonunit phases,
actual odd companion seeds, odd primitive phases, dyadic half parameters,
gap and cost constraints, and full affine tuple collisions.

Unit primitive phases at smaller indices remain open; so do larger
unequal companions, other profile families and axes, unrestricted
G1/G2/G3, and the global conjecture. The uniform maximal-index closure and
genuine companion-sum-through-ten bound remain proved. Continue after
verified milestones, committing and pushing both repositories.

**2026-09-08 — primitive factor two closes at arbitrary equal-companion lengths.**
`ChainForestProfileEqualFactorTwoArithmetic.lean` and
`ChainForestProfileEqualFactorTwo.lean` prove the genuine global bound
when the actual equal-companion index is `2^(a-1)`, for every `n>=67`
and every even modulus stratum. The maximal-axis hypothesis is explicit;
the original forest supplies all odd/unit phase and period data.

With `s=2^(a-1)`, `T=2s-1`, a unit phase selects `0<=v<T` and a signed
integer `nu` satisfying `2vq-r=2T*nu+1`. For `v<T-1`, the companion
weights `v+s,v` have at most `2a-1` coins. The exact signed identity
places the actual axis rival below `7K/4`; its complete representation
costs at most `L+1`, meeting the total budget. The exceptional weight
`v=T-1` forces `(s-2)q=Tm+1`. Equal companion weights `s-2` save two coins
each, paying for an actual rival below `3K`. The half-profile cost gives
the uniform error bound `8sn<K`, without a finite length cutoff.

Together with maximal-index closure, every remaining genuine equal-
companion counterexample now has `e+1<a` and primitive factor
`2^(a-e)>=4`. All bounded coefficients, odd/unit phases, original group
and scalar relations, dyadic parameters, and modulus-profile constraints
are retained. No phase, coin, or period coprimality premise is supplied.

Verification: 14 new audited exports; full Lean build **15,258 jobs**;
**4,234** standard-only or axiom-free declaration audits; **75,824**
forest tests. The 5,081 new cases cover every unit phase through equal
companion length 12, plus actual affine tuple collisions with odd seeds,
dyadic half parameters, both rival constructions, and negative as well
as nonnegative signed period coefficients.

Primitive factors at least four, larger unequal companions, other profile
families and axes, unrestricted G1/G2/G3, and the global conjecture remain
open. Continue after verified milestones and push both repositories.

**2026-09-08 — primitive factor four closes at arbitrary equal-companion lengths.**
`ChainForestProfileEqualFactorFourArithmetic.lean` and
`ChainForestProfileEqualFactorFour.lean` prove the genuine global bound
at actual equal-companion index `2^(a-2)`, for every `n>=67` and every
even modulus stratum. The maximal-axis hypothesis remains explicit.

The primitive unit phase selects one of two odd index steps, `1` or `3`.
An exact binary-block formula bounds both companion costs uniformly in
length. The lower range lies below `7K/4`; the upper quarter of step one
lies below `2K` and saves an additional companion coin. In the upper range
of step three, subtracting the actual half-profile lowers both companion
weights and adds its charge to the axis. The shifted rival still lies
below `7K/4`. Every case gives a full, affordable, distinct tuple rival.
All phase, period-deficit and half-profile data come from the original
forest; no phase, coin or period coprimality inputs are supplied.

Every remaining genuine equal-companion counterexample now has `e+2<a`
and primitive factor `2^(a-e)>=8`. Its bounded coefficients, odd/unit
phases, dyadic parameters, original scalar/group relations and complete
truncated modulus profile remain available.

Verification: 17 new audited theorem exports; full Lean build **15,260
jobs**; **4,251** standard-only or axiom-free declaration audits;
**85,981** forest tests. The 10,157 new cases cover every unit phase through
companion length 12, all three representation cases, and actual affine
cyclic-group tuple collisions with odd companion seeds and dyadic half
parameters. Generic binary-block, phase-selection, signed-error and
profile-subtraction lemmas are available for the remaining factors.

Primitive factors at least eight, larger unequal companions, other
profile families and axes, unrestricted G1/G2/G3, and the global conjecture
remain open. Continue after verified milestones and push both repositories.

The equal-companion family now closes uniformly. In dimensions `n >= 67`,
`ChainForestProfileEqualUniform.lean` proves the sharp global bound for every
genuine three-chain forest with a maximal even axis, odd companion seeds,
an axis-supported collision profile, and equal companion lengths. The
actual index is unrestricted. `ChainForestProfileEqualUniformArithmetic.lean`
uses three rational binary blocks for nonintegral phases and symmetric
companion weights around an odd dyadic boundary for integral phases.
All phases, period deficits and coin budgets come from the original forest;
there is no finite phase census or remaining equal primitive factor.

This milestone adds 22 audited theorems. Verification: 15,262 build jobs,
4,273 standard-only or axiom-free declaration audits, and 112,241 forest
tests in the companion `unique` repository, including 26,260 new cases.
Larger unequal companions, other axes and profile families, unrestricted
G1/G2/G3, and the global conjecture remain open.

For unequal companions, `ChainForestProfileUnequalEvenArithmetic.lean`
and `ChainForestProfileUnequalEven.lean` now exclude every even primitive
phase below the largest possible unequal index `2^(a-1)`. The top/half
midpoint has exact axis coefficient `(K+H-2)/2`; its companions save one
coin in either orientation. The genuine forest therefore supplies `F=1`
or an odd phase, preserving all previous bounded phase and profile data.
Verification: eight new theorem audits, 15,264 full build jobs,
4,281 standard-only or axiom-free audits, and 112,532 forest tests,
including 291 new cases. Largest unequal indices and odd phases remain open.

`ChainForestProfileUnequalStratum.lean` additionally derives the actual
modulus profile through the shorter companion half-width: for height `2^h`
and index `2^e`, every `j<=a-1-e` satisfies `2^(e+j) | N` exactly when
`j<=h`. Both orientations and the largest index are included, without
odd-denominator or period coprimality. The valuation is exact below the
terminal height; at or above it the theorem retains `2^(a-1) | N`.
Verification: six new theorem audits, 15,265 full build jobs,
4,287 standard-only or axiom-free audits and 112,763 forest tests,
including 231 new actual-phase and boundary tests. Uniform unequal rival
budgets and the unrestricted conjecture remain open.

The terminal unequal strata are sharper when the actual odd companion
seed is retained. `ChainForestProfileUnequalTerminal.lean` proves, for
`f=a-1-e>=1`, exact valuation `e+h` when `h<f`, divisibility by `2^a`
when `h=f`, and exact valuation `a-1` when `h>f`. The original genuine
forest supplies the primitive coefficient parity. The largest unequal
index stays explicit. Verification: five new theorem audits, 15,266
build jobs, 4,292 standard-only or axiom-free audits, and 112,987
forest tests including 224 new parity, stratum and hypothesis guards.
Uniform unequal rivals and the unrestricted conjecture remain open.

**2026-09-08 — uniform normalization and four-block arithmetic for unequal companions.**
`ChainForestProfileUnequalUniformArithmetic.lean` proves 26 general
arithmetic and signed-group lemmas. For short half-width `s`, long
half-width `t`, actual index `D`, and `D*F=s`, division of `D*m` by
`4*s-1` normalizes every `0<m<F*T` into companion weights with total
coin cost at most `a+b`. Either signed unit phase has a bounded leading
numerator; a nonpositive long numerator permits a top reflection.
The correct reflected axis coefficient is `K-1+V-Z`, including the
actual target offset. Both top and half reflections are proved as
signed group identities before nonnegativity is needed.

Four variable rational blocks handle any nonintegral numerator below
three primitive denominators. The actual half-profile cost pays for
an error constant `128*F*t^2` throughout the remaining range
`a+b>10`, `n>=67`, and `f<=a-2`. A general representation theorem now
turns that window into an affordable actual axis representation.
The exact nonintegral unit-phase condition includes the period width:
`T` must not divide `P+4*F*t*r`. Unit phases can be integral, and
reflected integral numerators can exceed two denominators.

Verification: 15,267 full build jobs; 4,318 declaration audits
(4,315 standard-only and three axiom-free); 114,150 passing forest
tests, including 1,163 new cases. Tests exercise arbitrary block
counts, normalized multipliers, actual cyclic-group identities,
target-offset reflection guards, and genuine integral unit phases.

This milestone supplies the uniform arithmetic layer. Continue by
consuming it in genuine forests for nonintegral unit phases, then
handle nonunit odd-denominator annihilators and integral unit phases.
The unequal global closure, other axes and profile families,
unrestricted G1/G2/G3, and Conjecture 1 remain OPEN. Continue after
each verified milestone and commit and push both repositories.

**2026-09-08 — nonintegral unequal unit phases close uniformly.**
`ChainForestProfileUnequalUnit.lean` consumes the normalized arithmetic
in actual valid forests. Both half orientations, all remaining unequal
length pairs, and every admissible actual dyadic index are covered,
including the largest index `F=1`. A signed primitive step or its actual
top reflection gives an affordable full tuple rival. Its group identity
and representation contradict validity.

The genuine extractor now returns
`UnequalCompanionUnitReducedPrimitiveData`: all previous bounded
coefficients, phase links, half-profile costs, group/scalar equations,
index alternatives and modulus profiles/strata are retained. In either
orientation its phase must be nonunit modulo `T`, or satisfy the integral
condition `T | P+4*F*t*r`. Here `P=t-1` in the short orientation and
`P=1-3*t` in the long orientation. No fixed width, fixed index or finite
phase census is used. Integral unit phases are explicitly retained.

Verification: six new theorem audits; 15,268 full build jobs;
4,324 declaration audits (4,321 standard-only and three axiom-free);
114,855 passing forest tests, including 705 new cases. Concrete groups
satisfy the actual period gap; representative rivals refine to full
collisions under chain reordering, multiplication by a unit and affine
translation. Even unit phases at the largest index are included.

Continue with nonunit odd-denominator annihilator multipliers and
integral unit boundaries. The unequal maximal-even-axis family is not
yet fully closed. Other axes and profile families, unrestricted G1/G2/G3,
and Conjecture 1 remain OPEN. Continue after every verified milestone
and commit and push both repositories.

**2026-09-08 — all nonunit unequal phases close uniformly.**
`ChainForestProfileUnequalNonunit.lean` supplies a bounded annihilator
multiplier for every nonunit phase in both orientations. A suitable
proper multiple of the odd denominator's annihilator puts the short
weight inside the actual half profile. The actual scalar equation,
together with the dyadic drop, forces its leading numerator to be
nonintegral. A direct rival or actual half-profile reflection then
fits the four-block budget and contradicts validity.

The genuine extractor now returns
`UnequalCompanionIntegralPrimitiveData`: every remaining unequal phase
is a unit modulo `T` and satisfies `T | P+4*F*t*r`. All earlier bounded
coefficients, index alternatives, actual orientation costs and equations,
and the complete modulus profiles/strata remain available. Both
orientations and all admissible indices are covered, including `F=1`.
No fixed-width or finite-phase premise is used.

Verification: thirteen new theorem audits; 15,269 full build jobs;
4,337 declaration audits (4,334 standard-only and three axiom-free);
115,097 passing forest tests, including 242 new cases. Actual groups
cover larger annihilator multiples, both index regimes, even nonunit
phases at the largest index, and full translated tuple collisions.
A long half-reflection example checks that branch explicitly. A
non-dyadic-drop guard demonstrates why automatic nonintegrality needs
the actual dyadic drop hypothesis.

Continue with integral unit boundaries and sharper normalized companion
coin bounds. This is the remaining unequal phase family for the current
maximal-even-axis route. Other axes and profile families, unrestricted
G1/G2/G3, and Conjecture 1 remain OPEN. Continue after every verified
milestone and commit and push both repositories.

**2026-09-08 — the complete maximal-even-axis companion family closes.**
`ChainForestProfileUnequalIntegralArithmetic.lean` and
`ChainForestProfileUnequalIntegral.lean` close every remaining integral
unit phase. Normalized direct companions save one coin; top-reflected
integral companions save two. A doubled dyadic boundary handles every
actual index, including `F=1`, with enough room on both sides of the
boundary. The reflected construction also covers a zero original
numerator and retains the actual target offset.

`even_axis_unequal_companions_global_bound` therefore proves the sharp
bound for all unequal companions. The combined theorem
`even_axis_maximal_companions_global_bound` covers both equal and unequal
lengths, with no phase, index, height or deficit restriction. Its explicit
hypotheses are a genuine rank-three forest at `n >= 67`, an even modulus,
a maximal even seed, two odd companion seeds, and an actual collision
profile supported on that even axis.

Verification: twenty-six new theorem audits; 15,271 full build jobs;
4,363 declaration audits (4,360 standard-only and three axiom-free);
119,654 passing forest tests, including 4,557 new cases. The new cases
cover 923 integral phase plans, 3,622 actual groups, dense tails on both
sides of the boundary, full collisions under affine transformations,
and both reflection and error signs.

Continue by consuming this closed family in the original three-escape
residual and treating the remaining axes and profile families. The
unrestricted G1/G2/G3 and Conjecture 1 remain OPEN. Continue after every
verified milestone and commit and push both repositories.

**2026-09-08 — maximal even-axis closure reaches original three-escape descent.**
`ChainForestProfileDominantResidual.lean` consumes the complete companion
closure using only the original two-odd-seed count. It constructs a
half-modulus child for original subglobal three-escape data with a
maximal even-axis profile, deriving companion parity and genuine
endpoints internally. The corresponding critical consumer retains the
explicit high-stratum premise `log2(n+1) <= s+1`.

The new original no-half extractor retains the entire one-to-three
profile family, all dyadic overflow shapes, parity and volume charges,
genuine endpoints, joint span, logarithmic companion bounds and actual
small dyadic index. Its uniquely longest chain is either an odd unit,
or even with a positive companion coefficient in EVERY actual profile.
Thus the closed maximal even-axis family is absent from this residual.

Verification: six new theorems, 15,272 full build jobs, and 4,369
complete declaration audits (4,366 standard-only and three axiom-free).
The preceding arithmetic milestone passed all 119,654 forest tests;
this milestone changes only Lean consumers and proof-status documents.

Continue with the positive-companion profile forms and the odd-unit
branch. Lower critical strata and unrestricted G1/G2/G3 and Conjecture 1
remain OPEN. Continue and push both repositories after every verified
milestone.

**2026-09-08 — positive compatible profiles have coupled power forms.**
`ChainForestProfileCompatibleSupport.lean` sharpens the remaining
compatible support using validity, uniformly over all lengths and seeds.
A positive even coefficient is a single positive binary power with every
other shifted side using at most two powers, or a sum of two positive
powers with every other shifted side dyadic. If both companion
coefficients are positive and even, they are actual interior chain
entries: `v_j+1=2^h`, `v_a=2^r`, `v_k=2^t`, with
`0<r<L_a`, `0<t<L_k`, and `2^h+2^r+2^t <= n`. No coordinate overflows.

The subglobal maximal-even-seed consumer derives a positive companion
from the completed axis closure and returns these coupled forms for
every compatible profile. These are constraints on the remaining
family, not a proof that it is empty.

Verification: seven new theorems; 15,273 full build jobs; 4,376 complete
declaration audits (4,373 standard-only and three axiom-free); 119,864
passing forest tests, including 210 new cases. The new tests exhaust
reflection survivors for 125 length triples, retain genuine examples
above binary for both support sizes, a two-power coefficient and a
single-arm overflow, and construct full collisions for forbidden forms
under coordinate permutations, unit multiplication and translation.

Continue by coupling these forms to the other profiles and their
quotient masses. Incompatible profiles, odd dominant units, lower
critical strata and unrestricted G1/G2/G3 and Conjecture 1 remain OPEN.
Continue and push both repositories after every verified milestone.

**2026-09-08 — a two-positive companion base is the entire profile family.**
`ChainForestProfileTwoPositiveSingleton.lean` eliminates every profile
coexisting with a base whose two companion coefficients are positive and
even. Rectangle disjointness first puts an overflow's dyadic excess
strictly beyond the old companion power. Shifting the original weights
by the profile difference then fits the original coin budget: the
overflowing companion costs at most one extra coin and the other saves
one, while the axis stays within its own length.

The singleton theorem holds in ANY abelian group with a valid
tuple, rank-three chain representation, a sufficiently wide joint box
and `n <= 2^(L_j)`. It requires no seed parity, finite-group, subglobal,
or terminal-endpoint assumption. In the even-cyclic setting with an even axis and odd companion seeds,
the surviving rectangle is explicit: `H=2^h`, `A=2^r`, `B=2^t`,
`H+A+B <= n`, and `2^n+H <= N+H*(A+1)*(B+1)`.

Verification: fourteen new theorems; 15,274 full build jobs; 4,390
complete declaration audits (4,387 standard-only and three axiom-free);
120,789 passing forest tests, including 925 new cases. Actual group
pairs across dimensions 13 through 67, several modulus scales and
offsets all give full shifted collisions. The arithmetic covers either
height ordering and the zero exponent on the new companion side;
a guard shows why the old companion must be even. Genuine examples
above binary retain exactly one profile and its exact height bias.

Continue with the remaining singleton rectangle and genuine boundary
packing, while retaining the one-positive, incompatible-only and
odd-unit branches. Unrestricted G1/G2/G3 and Conjecture 1 remain OPEN.
Continue and push both repositories after every verified milestone.

**2026-09-08 — all genuine three-chain forests close from length 67.**
`ChainForestLongBoundary.lean` removes the zero-pivot restriction from
boundary representations when `n <= 2^(L_a)`. Any nonzero boundary
represented in the ordinary box must be an actual dyadic tuple entry,
possibly in its own arm. A genuine endpoint therefore lies outside the
entire box. Short exterior columns no longer need a second wide arm.

`ChainForestBoundaryInterval.lean` extends the missing boundary along
its OWN seed: every `(2^(L_a)+t)*x_a`, with `0 <= t <= 2^(L_a-4)`,
is outside the box. A hypothetical representation either subtracts to
represent the forbidden boundary, or produces an actual rival using
four top coins and a small binary tail. High-box injectivity makes these
residues distinct. In a subbinary valid forest with `2*n+1 <= 2^(L_a)`,
the resulting count is
`2^n + 2^(L_a-4)+1 <= |G| + binomial(n+rank-1,rank)`.

For rank three and `n >= 67`, the largest arm alone pays this entire
binomial error. Thus EVERY genuine three-chain forest in ANY finite
abelian group satisfies `2^n <= |G|` in this range. No seed parity,
unit, supported profile, companion width, or index assumption remains.
The original critical three-escape consumer now gives half descent
in EVERY stratum for parent length at least 67, without a subglobal
premise or a supplied forest. All earlier singleton, one-positive,
incompatible-only and odd-unit profile branches in that class are
consumed by this stronger endpoint argument.

Verification: eighteen new theorems in two modules; 15,276 full build
jobs; 4,408 complete declaration audits (4,405 standard-only and three
axiom-free); 121,598 passing forest tests, including 809 new cases.
Tests check actual nonzero-pivot and same-axis group collisions through
parent length 65, all arm permutations and affine translations,
nonunit genuine forests with only one wide arm, wrapped valid examples,
all positive length triples from 67 through 300, and necessary endpoint,
nonzero-boundary and shift-size guards.

A large critical tuple without a half child now has at least FOUR
actual affine-doubling escapes at EVERY shift. Continue with that
original residual and parent lengths below 67. This does not extract a
three-escape shift from an arbitrary tuple. Conjecture 1 and unrestricted
G1/G2/G3 remain OPEN, with the same three global inputs. Continue and
push both repositories after each verified milestone.

**2026-09-08 — the large four-escape residual feeds the original G1 assembly.**
`G1LargeFourEscape.lean` defines `PrimitiveLargeFourEscapeDeleteStep`
and proves it equivalent to the existing primitive three-omission G1
obligation. It retains the old three-escape condition at every shift;
for parent length at least 67, it additionally retains four actual
escapes at every shift. The smaller parents, lengths five through 66,
remain inside the same obligation. The stronger condition is derived
from failure of half descent using the proved boundary-interval theorem.

Both the exact-stratum and global lower-bound assemblies now accept
this equivalent residual with exactly the original G2/G3 inputs. No
child-bound assumption or fourth gate is introduced. The definition is
an unproved obligation, not an asserted deletion theorem.

Verification: one audited definition and three new theorems; 15,277
full build jobs; 4,412 complete declaration audits (4,409 standard-only
and three axiom-free). The preceding full forest run passed 121,598
tests; this proof-only assembly change adds no executable test cases.
Continue with the four-escape residual and smaller-parent bounds.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and
push both repositories after every verified milestone.

**2026-09-08 — the genuine three-chain threshold is now 52.**
`ChainForestBoundaryIntervalSharp.lean` nearly doubles the missing
same-axis interval: every `(2^(L_a)+t)*x_a` with
`0 <= t < 2^(L_a-3)` lies outside the ordinary box. The all-ones tail
is excluded by this strict endpoint, saving the fourth top coin within
the chain's original budget. The interval has exactly `2^(L_a-3)`
distinct residues and pays the same arbitrary-rank binomial error.

The exact estimate `binomial(3*L+2,3) <= 2^(L-3)` holds from `L=18`.
Consequently every genuine three-chain forest of parent length at
least 52 satisfies `2^n <= |G|` in any finite abelian group. Original
critical data with at most three affine escapes now give half descent
in every stratum from that parent length. The existing equivalent
`PrimitiveLargeFourEscapeDeleteStep` has been updated accordingly:
its four-escape condition starts at parent length 52, and the smaller
three-escape range is now lengths five through 51. No new gate is added.

Verification: nine new theorems; 15,278 full build jobs; 4,421 complete
declaration audits (4,418 standard-only and three axiom-free); 122,426
passing forest tests, including 828 new cases. Tests exercise actual
rivals beyond the previous interval cutoff, all arm permutations and
affine translations, genuine nonunit forests, all positive length
triples from 52 through 180, and the strict tail endpoint. A valid
five-entry forest at modulus 28 supplies a guard against dropping the
length hypothesis entirely. The threshold 52 is a proved sufficient
bound; no optimality claim is made.

Continue with the original four-escape residual, its cycle/forest
structure and parent lengths below 52. All previously separated
three-chain profile cases from length 52 are consumed by this bound.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and
push both repositories after every verified milestone.

**2026-09-08 — original four-escape half descent closes from parent length 101.**
`ChainForestFourEscape.lean` proves that every genuine four-chain forest
of length at least 101 satisfies the binary bound in any finite abelian
group. The widest arm has length at least 26, where the exact quartic
binomial error fits its strict eighth-width missing interval.

The original four-escape data also have a complete cycle treatment from
parent length sixteen. Under failed half descent, actual doubling is
injective. The loss-free outside budget forces any cycle to have at
least seven vertices, so the existing exact-stratum cycle bound applies.
The remaining data are acyclic. Their actual escape set has exactly four
points; extracting its genuine forest and applying the binary bound gives
half descent from parent length 101, in EVERY critical stratum. No cycle,
forest, seed parity, modulus index or profile shape is supplied.

`G1LargeFiveEscape.lean` proves an equivalent form of the same primitive
G1 obligation and supplies its exact-stratum/global assemblies with the
same G2/G3 inputs. The retained escape conditions are now: at least three
at every shift for parents five through 51; at least four from 52; and
at least FIVE from 101. These conditions are derived from failed half
descent. The new residual definition is not an asserted deletion theorem
or an additional global gate.

Verification: eleven new theorems and one audited definition in two
modules; 15,280 full build jobs; 4,433 complete declaration audits
(4,430 standard-only and three axiom-free); 122,766 passing forest tests,
including 340 new cases. Tests cover all four-arm length partitions at
eight parent lengths from 101 through 200, the quartic recurrence,
actual genuine nonunit forests with very short companions, actual valid
four-escape cycles in smaller dimensions, the cycle/forest distinction
and guards against dropping the stated thresholds.

Continue with arbitrary escape-count thresholds and the original
five-escape residual, preserving the smaller-parent cases. Conjecture 1
and unrestricted G1/G2/G3 remain OPEN, 0/3. No bounded escape count has
been extracted from arbitrary critical tuples. Continue and push both
repositories after every verified milestone.

**2026-09-08 — original G1 half descent has a uniform escape-count threshold.**
`ChainForestEscapeThreshold.lean` works at ANY actual escape count `r`.
For a critical parent of length `k >= 4`, a shift satisfying
`binomial(k+r-1,r) <= 2^max(0,floor(k/r)-3)` gives half descent in every
stratum. No cycle, forest, seed normal form, supported profile or fixed
rank bound is supplied. The binomial inequality itself provides the
required cycle-size and boundary-width conditions; these are derived
inside the proof rather than added to the original input.

Consequently, at EVERY affine shift of an original critical no-half
tuple, its actual escape count satisfies both
`2^max(0,floor(k/r)-3) < binomial(k+r-1,r)` and the explicit estimate
`k < r^2*(floor(log_2(k))+1)+3*r`.
The latter uses the exact multichoose bound `binomial(k+r-1,r) <= k^r`,
so it needs no separate upper bound on `r` in the arithmetic lemma.

`G1QuantitativeEscape.lean` proves the quantitative primitive G1 input
EXACTLY equivalent to the existing primitive three-omission obligation.
It keeps the earlier three-/four-/five-escape restrictions in their
proved ranges; the average-length floor can be weaker than the earlier
widest-arm ceiling near lengths 52 and 101. Both assemblies retain
exactly the original G2/G3 inputs. This is a restriction of the same
open G1 gate, not an asserted deletion theorem or an additional gate.

Verification: fifteen new theorems and one audited definition in two
modules; 15,282 full build jobs; 4,449 complete declaration audits
(4,446 standard-only and three axiom-free); 123,306 passing forest tests,
including 540 new cases. Tests cover every positive rank up to each
parent length from four through 400, remainder-sensitive threshold
blocks through rank 24, actual genuine nonunit forests through rank 12,
general cycle budgets, large-parent arithmetic through one million,
and guards retaining the sharper earlier fixed-count ranges.

Continue with the quantitative original residual and transfer the
cycle/forest threshold to the odd-stratum input where doubling is
automatically injective. No small escape count has been extracted from
arbitrary critical tuples. Conjecture 1 and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after every milestone.

**2026-09-08 — the quantitative escape threshold now applies to original G2.**
`OddEscapeThreshold.lean` first proves every exact-stratum bound under
actual doubling injectivity and the single escape-count condition
`binomial(n+r-1,r) <= 2^max(0,floor(n/r)-3)`. The zero-escape case is
included through the proved one-escape theorem.

At ODD moduli, valid-tuple injectivity makes doubling automatically
injective. The same scalar condition therefore gives the original odd
bound `2^n-1 <= N`, without a G1 premise, supplied cycle, forest, seed
normal form or unit assumption. Every hypothetical original odd
counterexample of length at least four now satisfies, at every shift,
`2^max(0,floor(n/r)-3) < binomial(n+r-1,r)` and
`n < r^2*(floor(log_2(n))+1)+3*r` at its ACTUAL escape count.

`G2QuantitativeEscape.lean` proves this quantitative restriction EXACTLY
equivalent to the existing odd-stratum G2 obligation. All smaller
sizes remain in that same gate. The joint exact-stratum/global
assemblies now use quantitative G1, quantitative G2, and precisely the
original G3 input. None of the three unrestricted gates is closed.

Verification: nine new theorems and one audited definition in two
modules; 15,284 full build jobs; 4,459 complete declaration audits
(4,456 standard-only and three axiom-free); 123,413 passing forest tests,
including 107 new cases. Actual odd cycles check zero escapes and
nonunit embeddings, odd genuine forests cover arbitrary tested ranks,
and injective even models check the all-stratum core. The valid even
four-entry tuple modulo 12 shows why the original odd conclusion must
retain oddness (or an appropriate exact stratum).

Continue with the unconditional global counterexample split and the
G3 branch with actual injective doubling, retaining doubled collisions
explicitly. No small escape count is extracted from arbitrary tuples.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and
push both repositories after every verified milestone.

**2026-09-08 — global counterexamples retain an actual opposite pair or quantitative escapes.**
`GlobalEscapeThreshold.lean` proves the global lower bound directly for
actual injective doubling when one shift satisfies
`binomial(n+r-1,r) <= 2^max(0,floor(n/r)-3)`, for `n >= 4`.
No G1/G2/G3 input is assumed. Every hypothetical global counterexample
therefore has an actual opposite pair at an even modulus, OR satisfies
both `2^max(0,floor(n/r)-3) < binomial(n+r-1,r)` and
`n < r^2*(floor(log_2(n))+1)+3*r` at every shift's actual escape count.

At the original exceptional G3 modulus `2*globalBound(n-1)`, the same
scalar condition excludes the actual injective-doubling branch. Without
injectivity, every hypothetical valid G3 tuple retains an actual
opposite pair at `globalBound(n-1)` OR the all-shift quantitative bounds.
The opposite-pair branch remains OPEN. No no-half-child assumption is
inserted: the exceptional half modulus already admits a valid child.

`G3QuantitativeEscape.lean` proves this restricted obstruction EXACTLY
equivalent to original G3, retaining all small dimensions. Both global
and exact-stratum assemblies now accept precisely three proved
equivalent quantitative G1/G2/G3 inputs. All three remain unproved.

Verification: ten new theorems and one audited definition in two
modules; 15,286 full build jobs; 4,470 complete declaration audits
(4,467 standard-only and three axiom-free). These proof-only consumers
add no Python tests; the preceding complete forest run passed 123,413
tests. Next, retain the actual extremal half child through opposite-pair
deletion and investigate its structure without assuming a canonical
endpoint classification. Conjecture 1 and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after each verified milestone.

**2026-09-08 — actual half deletion preserves every affine escape count.**
`ActualEscapeDescent.lean` proves that deleting a coordinate identified
with a retained partner under an additive map preserves all existing
targets. Child escapes embed into the parent's escape set with the
deleted coordinate erased. The actual count never increases, and it
strictly decreases if the deleted coordinate was an escape. Equal
doubles have the same escape status at every shift.

The cyclic opposite-pair theorem combines this count bound, at all
projected shifts simultaneously, with validity of the ACTUAL half child.
It applies at G3's exact half modulus `globalBound(n-1)`; it does not
classify the child or exclude the opposite-pair branch by itself.
Seven new theorems; full build: 15,287 jobs; complete audits: 4,477
(4,473 standard-only and four axiom-free). No new Python tests for
these proof-only structural consumers; preceding complete forest run:
123,413 passing. Next: cut the unique collision away from a longest
path and extract a widest genuine forest arm. Conjecture 1 and all
three unrestricted gates remain OPEN, 0/3. Continue after each milestone.

**2026-09-08 — the scalar escape threshold now includes opposite pairs.**
`CollisionForest.lean` extracts an actual forest from every acyclic
valid tuple in a group with at most one nonzero involution. Protect a
longest path to a genuine escape, then cut the unique doubled collision
outside that path. The forest has at most `r+1` arms, and a widest arm
still ends at a genuine escape. Its proved exterior interval pays the
binomial packing error; no forest, rank, or injectivity is supplied.

`CollisionEscapeThreshold.lean` combines this extraction with the
existing cycle budget. For every cyclic valid tuple of length `n >= 4`,
one shift satisfying `binomial(n+r,r+1) <= 2^max(0,floor(n/(r+1))-3)`
now forces BOTH the original exact-stratum and global lower bounds.
No G1/G2/G3, no-half-child, or doubling-injectivity premise is assumed.
The earlier stronger `r` threshold remains available when doubling is
injective, including original odd G2 and G1 no-half data.

Consequently EVERY hypothetical global or exact-stratum counterexample,
including every original G3 tuple with an actual opposite pair, satisfies
at EVERY shift both `2^max(0,floor(n/(r+1))-3) < binomial(n+r,r+1)` and
`n < (r+1)^2*(floor(log_2(n))+1)+3*(r+1)` at its actual escape count.
The opposite pair is no longer an alternative to this quantitative
restriction. The unrestricted G3 obstruction is still OPEN: no suitably
small escape count is extracted from arbitrary tuples.

Verification: fourteen new theorems in two modules; 15,289 full build
jobs; 4,491 complete audits (4,487 standard-only and four axiom-free);
123,459 passing forest tests, including 46 new tests. Independent scans
check every cut of small acyclic maps with at most one collision;
actual valid even tuples check all affine shifts, and counterexamples
show why an arbitrary cut or multiple collisions would invalidate the
argument. Next: sharpen the rounded-up threshold and update the exact
G3 residual using the unconditional all-shift bound. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after every verified milestone.

**2026-09-09 — rounded-up escape threshold and unconditional quantitative G3.**
`CollisionEscapeCeiling.lean` sharpens the collision-inclusive scalar
condition to `binomial(n+r,r+1) <= 2^max(0,ceil(n/(r+1))-3)`. It proves
that this rounded-up charge still supplies the cycle cutoff and the
wide exterior interval. Every original exact-stratum and global bound
continues to follow without doubling injectivity, half descent, or a
conjectural input. All actual opposite pairs are included.

Every hypothetical original global, exact-stratum, or G3 counterexample
therefore violates this stronger ceiling charge at every shift and
retains `n < (r+1)^2*(floor(log_2(n))+1)+3*(r+1)`. The existing
`G3QuantitativeEscape.lean` now uses this unconditional all-shift
restriction: an opposite pair is no longer a separate alternative in
its definition. Exact equivalence to original G3 and both assemblies
with precisely three inputs are rechecked. All smaller dimensions and
the stronger earlier injective `r` bounds remain available.

Verification: eight new theorems and the revised existing G3 definition,
equivalence and assembly; 15,290 full build jobs; 4,499 complete audits
(4,495 standard-only and four axiom-free); 123,865 passing forest tests,
including 406 new tests. Boundary checks include the ceiling-six case,
small-dimension guard, rank monotonicity, and the improvements at
`(n,r)=(52,2),(53,2),(101,3),(102,3),(103,3)` missed by the floor charge.
Next: package the whole two-/three-escape global/G3 classes from lengths
52/101, then address the remaining arbitrary high-escape tuples.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and
push both repositories after each verified milestone.

**2026-09-09 — whole two-/three-escape global classes close from lengths 52/101.**
`GlobalFewEscape.lean` proves the original global and EVERY exact-stratum
bound for every valid tuple with at most TWO actual affine escapes at
some shift when `n >= 52`, and at most THREE when `n >= 101`. These
classes include opposite pairs and all actual cycle/forest geometries;
no injectivity, failure of half descent, or normal form is supplied.

Every hypothetical original global or exact-stratum counterexample
therefore has at least three escapes at EVERY shift from length 52,
and at least four from length 101. Original exceptional G3 tuples
inherit the same lower counts, including the opposite-pair case. The
earlier stronger G1 no-half counts (four from 52, five from 101), odd
injective bounds, and arbitrary-count ceiling obstruction remain.

Verification: twelve new proof-consumer theorems; 15,291 full build
jobs; 4,511 complete declaration audits (4,507 standard-only and four
axiom-free). No new Python tests: the preceding complete run passed
123,865 tests, including the ceiling boundary and later-block checks
used here. Next: sharpen the actual forest error using truncated
corner side lengths, to handle one long genuine chain with arbitrary
remaining coordinates. This is a new proposed direction, not a proved
class. Arbitrary high-escape tuples and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after every milestone.

**2026-09-09 — one long genuine chain controls arbitrary remaining coordinates.**
`ChainForestTruncatedInterval.lean` charges the proved exterior interval
against the actual rectangular error `product_i min(n,2^L_i)`. For a
selected arm of length `m`, this error is at most `n*2^(n-m)`, regardless
of the number or lengths of the other arms.

The module constructs an actual forest from ANY embedded affine
chain and arbitrary remaining coordinates, treating those coordinates
as singleton arms. If `m >= 4`, the chain's next affine double is absent
from the entire tuple, and `n*2^(n-m) <= 2^(m-3)`, then `2^n <= |G|` in
EVERY finite abelian group. The explicit sufficient length condition is
`n+floor(log_2(n))+4 <= 2*m`. No total escape-count bound, cyclicity,
doubling injectivity, or normal form for the other coordinates is used.

At a cyclic modulus below `2^n`, any actual chain passing that cutoff
therefore has an ACTUAL continuation somewhere in the original tuple.
Its target may rejoin the chain; genuine termination is essential to
the binary bound. This is a new high-escape class, beyond the preceding
binomial threshold, and does not close arbitrary G1/G2/G3.

Verification: twelve new theorems; 15,292 full build jobs; 4,523 complete
audits (4,519 standard-only and four axiom-free); 124,616 passing forest
tests, including 751 new tests. Independent convolution counts check
the truncated error, high-escape models separate this bound from the
binomial charge, and actual valid subbinary chains show why the genuine
endpoint hypothesis cannot be dropped. Next: follow the mandatory
continuation to an internal rejoin, extract an actual cycle, and control
its incoming chain using the existing zero-sum-fibre bound. These next
steps are not yet claimed as completed. Conjecture 1 and unrestricted
G1/G2/G3 remain OPEN, 0/3; continue and push both repositories after
each verified milestone.

**2026-09-09 — arbitrary endpoints in the whole long-chain class.**
`LongChainCycle.lean` proves the original global and every exact-stratum
lower bound for any valid cyclic tuple of length `n >= 16` containing an
actual affine chain of length `m` with `n+2*floor(log_2(n)) <= 2*m`.
The endpoint and remaining coordinates are arbitrary. No escape-count,
doubling-injectivity, no-half-child, or unit-seed hypothesis is needed.
The module also directly excludes every original G3 tuple in this class.

At subbinary modulus, a maximal extension of the actual long chain must
rejoin itself. The extracted cycle has an incoming tail of length `t`;
validity and the zero-sum-fibre bound give `2^t <= p`, where `p` is the
extended chain length. Thus `t <= floor(log_2(n))`, and the actual cycle
contains at least half the original tuple. The existing majority-cycle
lower bounds finish the proof. Every global or exact-stratum
counterexample of length at least 16 therefore has EVERY actual affine
chain satisfying `2*m < n+2*floor(log_2(n))`.

Verification: eleven new theorems; 15,293 full build jobs; 4,534 complete
audits (4,530 standard-only and four axiom-free); 125,103 passing forest
tests, including 487 new tests. Actual endpoint models check all starting
coordinates, tails, rejoins, shifts and signs; arithmetic tests check the
majority cutoff, with guards for uncontrolled tails and invalid tuples.
The arbitrary high-escape, short-chain residual remains open. Conjecture 1
and unrestricted G1/G2/G3 remain OPEN, 0/3; continue and push both
repositories after each verified milestone.

**2026-09-09 — combined coverage by arbitrary partial chain families.**
`PartialChainForest.lean` completes any actual disjoint family of `r`
affine chains, with total covered length `S`, by singleton arms on
exactly the remaining `n-S` coordinates. Every selected arm and
endpoint is retained. The truncated error is at most
`(product_i min(n,2^L_i))*2^(n-S)`, hence at most `n^r*2^(n-S)`.

A selected genuine arm of length `m >= 4` therefore gives `2^n <= |G|`
whenever `n^r*2^(n-S) <= 2^(m-3)`. The sharper product criterion is also
available with the explicit wide-arm hypothesis. A sufficient scalar
condition is `n-S+r*(floor(log_2(n))+1)+3 <= m`. All remaining
coordinates are arbitrary, and no bound on their actual escapes is
assumed. At subbinary cyclic modulus the selected endpoint must have
an actual continuation, possibly into another selected arm or itself.
For equal two-arm families this reaches roughly one-third length,
beyond the preceding single-arm cutoff.

Verification: six new theorems; 15,294 full build jobs; 4,540 complete
audits (4,536 standard-only and four axiom-free); 125,729 passing forest
tests, including 626 new cases. Tests retain original arm indices,
check exact completion and charge inequalities, separate combined
coverage from individual-chain bounds, and guard against overlapping
chains. The arbitrary-endpoint maximal-family cycle extraction is
still pending. The earlier whole long-chain class remains proved;
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and
push both repositories after every verified milestone.

**2026-09-09 — arbitrary endpoints for two chains beyond a one-third cutoff.**
`TwoChainCoverCycle.lean` proves the original global and every
exact-stratum lower bound from ANY two disjoint actual affine chains
of equal length `m >= 4` satisfying
`n+2*floor(log_2(n))+5 <= 3*m`. Their endpoints and all remaining
coordinates are arbitrary. The direct original G3 exclusion is also
proved. No genuine endpoint, small escape count, doubling injectivity,
no-half-child hypothesis or unit seed is assumed.

The more general unequal-length result uses
`n^2*2^(n-(p+q)) <= 2^(p-3)` and
`n+4*floor(log_2(n)) <= 2*(p+q)`, with `p >= 4`.
Maximize the first chain while preserving total covered length and a
disjoint second chain. A new target extends the first; a target in the
second transfers its entire suffix while retaining the disjoint prefix.
Both operations strictly increase the first length, so its final target
must rejoin itself. Validity bounds both the incoming tail and the
disjoint second chain logarithmically. The extracted cycle therefore
contains at least half the original tuple, and existing majority-cycle
bounds finish. For example, two disjoint length-39 chains suffice at
`n=100`, where either chain alone is below the earlier cutoff.

Verification: fourteen new theorems; 15,295 full build jobs; 4,554
complete audits (4,550 standard-only and four axiom-free); 127,079
passing forest tests, including 1,350 new cases. Actual even-modulus
forks check every suffix splice in the tested ranges; valid gap tuples
check coverage-preserving extensions, splices, internal rejoins and
majority cycles under all allowed strata, signs and tested shifts.
No tuple census enters the Lean proof. The next direction is to retain
arbitrary numbers of shorter chains in a maximal family. Arbitrary
high-escape tuples still need not supply sufficient combined coverage.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3; continue and
push both repositories after every verified milestone.

**2026-09-09 — arbitrary-arity actual chain families with unrestricted endpoints.**
`MaximalChainFamily.lean` proves the original global and every
exact-stratum lower bound from ANY `r >= 2` disjoint actual affine
chains of equal length `m >= 4` when
`n+r*floor(log_2(n))+r+3 <= (r+1)*m`. Original G3 is directly excluded
in the same class. The number of selected chains is unbounded; every
seed, endpoint and remaining coordinate is arbitrary, at a common
affine shift. No small escape count or injective-doubling premise occurs.

The general unequal-length family has total cover `S` and selected
arm length `m`. It suffices that `n^r*2^(n-S) <= 2^(m-3)` and
`n+2*r*floor(log_2(n)) <= 2*S`. Empty members are allowed internally.
The proof maximizes a designated chain while preserving the initial
coverage and all seeds. New targets extend it; a target in another
member transfers that member's suffix, retaining its possibly empty
prefix and every unaffected member. Explicit maps to the old indices
prove disjointness and exact coverage preservation. Maximality therefore
forces an internal rejoin. Each remaining chain and the incoming tail
are logarithmic, leaving an actual majority cycle. The final theorems
accept ordinary embeddings of the selected disjoint family.

For example, three length-31 chains suffice at `n=100`, four length-47
chains at `n=200`, and five length-75 chains at `n=400`; the previous
cutoffs fail for every smaller subfamily of those lengths.
Verification: one definition and sixteen theorems; 15,296 full build
jobs; 4,571 complete audits (4,567 standard-only and four axiom-free);
128,398 passing forest tests, including 1,319 new cases. Actual fork
splices retain arbitrary additional members and empty prefixes. Valid
gap models exercise arbitrary selected positions, several arities,
all allowed strata, signs and tested shifts through actual rejoin.
The next direction is to charge all remaining chains jointly rather
than use a separate logarithmic bound for each. Sufficient combined
coverage is still not extracted from arbitrary high-escape tuples.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3; continue and
push both repositories after every verified milestone.

**2026-09-09 — joint cycle growth sharpens actual family coverage.**
`FamilyAggregateCycle.lean` charges the incoming prefix and EVERY
surviving chain to one strict binary-growth budget. A nonempty actual
cycle of length `c` disjoint from family lengths `L_i` forces
`sum_i(2^L_i-1) < c+sum_i L_i`. The argument retains empty members,
arbitrary affine seeds, and all original coordinate indices.

At maximal rejoin, let `P` be the extended covered length, `K=P-c`
the total outside length, and `r` the number of selected members.
For EVERY depth `t`, put `B=2^t` and `D=t*B-(B-1)`. Joint growth gives
`B*K < P+r*D`. Consequently, initial covered length `S` suffices for
a majority cycle whenever `B*n+2*r*D <= 2*(B-1)*S` for some depth.
Together with the existing continuation charge
`n^r*2^(n-S) <= 2^(m-3)`, for a selected arm `m >= 4`, this proves the
original global, every exact-stratum and direct G3 bounds. Endpoints
and all unselected coordinates remain unrestricted.

This improves the separate logarithmic allowance per member. At
`n=128`, lengths `(68,9)` satisfy the depth-four criterion although
both the earlier single-chain and separate-logarithm coverage cutoffs
fail. Further checked separations include `(132,11)` at `n=256`,
`(68,8,8)` at `n=128`, and `(260,11,10,10)` at `n=512`.
Verification: ten new theorems; 15,297 full build jobs; 4,581 complete
audits (4,577 standard-only and four axiom-free); 128,861 passing
forest tests, including 463 new cases. Tagged coin splitting checks
the joint interval independently; actual valid gap models retain the
incoming prefix and every other surviving member in the same budget.
Next retain the ACTUAL truncated product through maximal continuation,
so short members need not pay a full factor of `n`. Arbitrary tuples
still need not supply sufficient selected structure. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3; continue and push both
repositories after every verified milestone.

**2026-09-09 — actual truncated profiles survive maximal continuation.**
`ChainFamilyProfile.lean` retains the exact partial-family error
`E = product_i min(n,2^L_i)*2^(n-S)`, where `S=sum_i L_i`.
A selected arm of length `m >= 4` with `2*n+1 <= 2^m` keeps its corner
side saturated at `n`. Controlled extension and suffix splicing only
shorten other members and never reduce total coverage. Thus `E` cannot
increase throughout the maximal-family argument. Removing empty
members changes neither coverage nor the product.

The original global, every exact-stratum and direct G3 bounds now
follow from `E <= 2^(m-3)` together with the existing collective
coverage condition `B*n+2*r*D <= 2*(B-1)*S`, where `B=2^t` and
`D=t*B-(B-1)` at any chosen depth. All chain seeds, endpoints and
unselected coordinates remain arbitrary at a common affine shift.
The previous `n^r` charge and theorem interfaces remain available.

New examples include one length-69 chain and four length-4 chains at
`n=128`, one length-134 chain and eight length-4 chains at `n=256`,
and one length-262 chain and eight length-5 chains at `n=512`.
These pass the exact profile condition while failing the full-factor
charge and earlier single-chain cutoff. Shorter selected companion
families also fail the tested collective coverage conditions.
Verification: one definition and nine theorems, including two stronger
controlled helpers with wrappers preserving the old interfaces;
15,298 full build jobs; 4,591 complete audits (4,587 standard-only and
four axiom-free); 129,516 passing forest tests, including 655 new cases.
Tests check exact error monotonicity, empty-member identities and
actual valid-gap continuation/splicing with all surviving prefixes.
Next examine whether the existing below-half-cycle bounds remove the
separate majority-cover requirement. That strengthening is not yet
proved. Arbitrary tuples still need not provide a sufficiently charged
family; Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after every verified milestone.

**2026-09-09 — single-chain charge without separate coverage.**
`ChainChargeWithoutCover.lean` proves the original global, every
exact-stratum and direct G3 bounds from any actual affine chain of
length `m >= 4` satisfying `n*2^(n-m) <= 2^(m-3)`. Its endpoint and
all remaining coordinates are arbitrary. No separate majority-cover
premise is needed. In particular, `n+floor(log_2 n)+4 <= 2*m`
suffices, without the previous `n >= 16` assumption.

Maximal singleton continuation yields a cycle of length `c` inside a
chain of length `p`, with `2^(p-c) <= p`. If `n >= 2*c+2`, the scalar
charge implies `3*2^(n-2*c) <= c`. The existing all-modulus exponential
deficit theorem then forces the binary bound. Thus below binary
modulus the actual cycle must satisfy `n <= 2*c+1`, and the existing
half-sized cycle consumers give every original bound. The argument
also covers the odd-dimensional one-extra case.

The charge applies to lengths 69, 134 and 262 in dimensions 128, 256
and 512, respectively, improving the prior two-logarithm single-chain
cutoff. Verification: nine theorems; 15,299 full build jobs; 4,600
complete audits (4,596 standard-only and four axiom-free); 130,702
passing forest tests, including 1,186 new cases. Checks include actual
valid-gap cycles at all starts, signs, shifts and admissible strata,
and a nonvacuous below-half arithmetic example.
Next remove the coverage premise for general exact-profile families
by reducing their maximal-family error to the selected single-chain
charge. Arbitrary charged-family extraction remains unproved.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and
push both repositories after every verified milestone.

**2026-09-09 — exact family charge without width or coverage premises.**
`ChainFamilyWithoutCover.lean` proves the original global, every
exact-stratum and direct G3 bounds for any actual embedded family
with a selected length `m >= 4` and
`product_i min(n,2^L_i)*2^(n-sum_i L_i) <= 2^(m-3)`.
The common affine shift, seeds, endpoints and remaining coordinates
are arbitrary. Empty members are allowed. Neither the old width
condition nor a separate collective coverage condition is required.

The charge itself forces `2*n+1 <= 2^m`. The maximal-family theorem
now exposes its preserved error bound, while its old interface remains
available. An internal rejoin supplies an actual cycle inside the
selected member. Every disjoint member then has length at most
`floor(log_2 n)`, so its truncated factor is exactly its power of two.
The entire error collapses to `n*2^(n-p)` for the extended selected
length `p`. The charge-only single-chain theorem completes all three
original consumers. No unrestricted family-extraction claim is used.

Verification: eight theorems, including the stronger continuation
helper; 15,300 full build jobs; 4,608 complete audits (4,604 standard-only
and four axiom-free); 131,071 passing forest tests, including 369 new
cases. Checks retain seeds through actual extension/splicing, verify
profile reduction with empty members, and cover families whose initial
selected chain alone cannot pay the charge.
Next feed the all-shift, all-family charge obstruction into the
existing original G1/G2/G3 reductions, then study extraction from
arbitrary critical tuples. The scalar escape bounds alone do not yet
supply a charged family. Conjecture 1 and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after every milestone.

**2026-09-09 — all-family profile obstruction in the original gates.**
`ChainProfileGates.lean` proves that every hypothetical global, exact
stratum, odd-stratum or exceptional G3 counterexample fails the exact
charge at every affine shift and every embedded finite chain family.
For every selected member with `m >= 4`, necessarily
`2^(m-3) < product_i min(n,2^L_i)*2^(n-sum_i L_i)`.
Empty members and arbitrary endpoints remain included.

The original G1, G2 and G3 obligations are each proved equivalent to
their existing quantitative-escape restriction with this additional
necessary profile condition. The three new residual names are
`PrimitiveChainProfileDeleteStep`, `OddChainProfileLowerBound` and
`ExceptionalChainProfileObstruction`. Exact-stratum and global induction
still use precisely the same three open inputs, with all earlier
escape conditions and small dimensions retained. No gate is asserted.

Verification: four definitions and nine theorems; 15,301 full build
jobs; 4,621 complete audits (4,617 standard-only, four axiom-free).
The unchanged numerical forest checks retain their latest complete
131,071-pass result from the preceding milestone; this change adds
only Lean reductions and documentation.
Next investigate the bounded coefficient corner, retaining its
sum constraint rather than only its enclosing rectangle. Any sharper
charge must be preserved through actual continuation and remain strong
enough for the cycle-deficit argument. Arbitrary critical-tuple
extraction is still unproved. Conjecture 1 and unrestricted G1/G2/G3
remain OPEN, 0/3. Continue and push both repositories after milestones.

**2026-09-09 — twice the post-rejoin error allowance.**
`ChainRejoinDoubleCharge.lean` proves the original global, every
exact-stratum and direct G3 bounds for an actual internally rejoining
chain of length `p >= 4` satisfying `n*2^(n-p) <= 2^(p-2)`.
The remaining coordinates are arbitrary. This doubles the previous
error allowance. The actual rejoin is an explicit premise; no stronger
continuation theorem is claimed for this weaker charge.

The incoming tail still satisfies `2^(p-c) <= p`. If the cycle has
`n >= 2*c+2`, the weaker charge forces the tail to have length at least
four. Then `3*(p-c) <= 2^(p-c) <= p`, giving `2*p <= 3*c` and still
forcing `3*2^(n-2*c) <= c`. The existing exponential-deficit theorem
excludes this branch below binary modulus. The older single-chain
arithmetic theorem now calls this stronger estimate, preserving its
interface and avoiding duplicate proofs.

Verification: six new theorems; 15,302 full build jobs; 4,627 complete
audits (4,623 standard-only and four axiom-free); 131,684 passing forest
tests, including 613 new cases. Newly admitted arithmetic examples
include lengths 133, 518 and 2055 at dimensions 256, 1024 and 4096.
Next prove the sharper bounded-corner count and preserve it through
actual continuation. A reflection estimate should compare the old
rectangle with twice that corner after a rejoin, matching this theorem.
That geometric integration remains unproved. Conjecture 1 and all
unrestricted G1/G2/G3 gates remain OPEN, 0/3. Continue and push both
repositories after every verified milestone.

**2026-09-09 — bounded corner counting and genuine endpoints.**
`BoundedChainCorner.lean` retains the total-weight cutoff in the actual
coefficient corner: `C(n,L)` counts vectors with
`0 <= z_i < min(n,2^L_i)` and `sum_i z_i < n`. The partial-family error
is `C(n,L)*2^(n-sum_i L_i)`. This count is bounded by both the previous
truncated product and the full stars-and-bars binomial.

A saturated selected side, shortening other members and growing
coverage preserve this smaller error. Its charge still forces the
selected width automatically. The upper-simplex collision law now
charges genuinely avoided residues to this exact corner. Consequently,
a positive actual partial family with a genuine selected endpoint,
selected length `m >= 4`, and error at most `2^(m-3)` satisfies the full
binary bound. All other endpoints and unselected coordinates are
arbitrary. Reflection also proves that a box with total side deficit
below `2*n` has size at most twice its small-sum corner.

Strict charge improvements include profiles `(40,36)` at `n=100`,
`(70,4)` at `n=130`, `(135,4)` at `n=259`, and `(263,4)` at `n=514`.
Verification: two definitions and thirteen theorems; 15,303 full build
jobs; 4,642 complete audits (4,638 standard-only, four axiom-free);
131,965 passing forest tests, including 281 new cases. The dynamic
count agrees with exhaustive small-box enumeration; tests cover
reflection, monotonicity, empty-member counts and genuine valid models.
Next remove the genuine-endpoint premise via maximal continuation,
retaining this smaller error and using the joint cycle weight budget
with reflection to reach the doubled post-rejoin charge theorem.
That arbitrary-endpoint integration is not yet proved. Conjecture 1
and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both
repositories after every verified milestone.

**2026-09-09 — bounded-corner charge with arbitrary endpoints.**
`BoundedFamilyContinuation.lean` proves the original global, every
exact-stratum and direct G3 bounds from
`C(n,L)*2^(n-sum_i L_i) <= 2^(m-3)`, for any selected length `m >= 4`.
Here `C` counts the bounded coefficient vectors with total weight below
`n`. The common shift, all seeds, endpoints and unselected coordinates
are arbitrary; empty members are allowed. There are no additional
width or coverage premises.

Removing empty members permits the genuine-endpoint theorem to force
continuation. Controlled extension and splicing preserve the smaller
error through a maximal family. At an internal rejoin, the actual
cycle bounds the joint power weight of every other member. Consequently
the truncated rectangle has total side deficit below `2*n`, and its
cardinality is at most twice the bounded corner. The rectangle equals
the selected single-chain error, so the doubled post-rejoin theorem
proves all original bounds. The binomial charge
`choose(n+r-1,r)*2^(n-sum_i L_i) <= 2^(m-3)` also suffices directly.

Verification: eleven theorems; 15,304 full build jobs; 4,653 complete
audits (4,649 standard-only, four axiom-free); 132,019 passing forest
tests, including 54 new actual-continuation cases. The factor-two
comparison is asymptotically sharp on valid-gap profiles: their
rectangle has size `n^2` while twice the bounded corner is `n*(n+1)`.
The earlier strict profile improvements now give original bounds
without a genuine-endpoint assumption.
Next strengthen the original counterexample restrictions using this
smaller error and the existing all-depth cycle/escape budgets.
Arbitrary sufficiently charged-family extraction is still unproved.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and
push both repositories after every verified milestone.

**2026-09-09 — sharper linear escape threshold for actual cycles.**
`LinearCycleEscape.lean` proves the original global, every exact-stratum
and direct G3 bounds whenever a valid tuple of dimension `n >= 3`
contains an actual nonempty affine cycle and has at most `r` escapes
at that shift, with `5*r+1 <= n`. This improves the earlier uniform
cycle condition `6*(r+1) <= n`, without doubling injectivity or a
failed half-descent premise.

The first growth layer excludes a singleton cycle in this range.
The second gives `4*k < n+5*(r+1)` for the outside count `k`.
The new dimension condition directly forces `k <= m+1`, where `m`
is the cycle length, so the original half-sized cycle bounds apply.
Conversely, every original global, exact-stratum or exceptional
counterexample with an actual cycle at a shift satisfies `n < 5*r+1`
there. This is a cycle-conditioned restriction, not an improved bound
for every tuple with `r` escapes.

Verification: seven theorems; 15,305 full build jobs; 4,660 complete
audits (4,656 standard-only, four axiom-free); 132,709 passing forest
tests, including 690 new cases. Tests cover both layer inequalities,
the newly admitted dimension range, boundary arithmetic and actual
cycles at every edge-supporting shift in valid-gap models.
Next combine this cycle restriction and bounded-corner charge failure
in equivalent forms of the original three gates. Arbitrary sufficiently
charged-family extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both
repositories after every verified milestone.

**2026-09-09 — combined bounded-corner and cycle restrictions in the original gates.**
`BoundedCornerGates.lean` retains failure of the exact bounded-corner
charge for every embedded affine chain family at every shift, together
with `n < 5*r+1` at every shift supporting an actual nonempty cycle.
Every original global, exact-stratum, odd or exceptional counterexample
satisfies this combined obstruction. It implies the earlier rectangular
profile restriction.

All three original gates are equivalent to their versions carrying
this stronger obstruction and all previous quantitative escape
restrictions. The exact-stratum and global induction assemblies retain
precisely the same three open inputs, including their small dimensions.
These are proved equivalences, not proofs of the inputs.

Verification: four definitions and ten theorems; 15,306 full build jobs;
4,674 complete audits (4,670 standard-only, four axiom-free). The latest
unchanged forest suite has 132,709 passing tests; this milestone changes
only Lean gate adapters. Next extract complete actual forests in the
low-escape acyclic case. Arbitrary sufficiently charged-family extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after every verified milestone.

**2026-09-09 — complete actual obstructing forests at low-escape shifts.**
`ObstructingChainForest.lean` extracts a complete affine forest from an
acyclic valid tuple below binary size in any finite abelian group with
at most one nonzero involution. It retains all coordinates, positive
chain lengths summing to `n`, the affine seeds, and a longest arm whose
endpoint genuinely escapes. The forest endpoints contain all true
escapes and add at most one collision cut. Its longest arm strictly
fails the bounded-corner charge, including positive lengths below four.

Every original global, exact-stratum, odd or exceptional counterexample
supplies this forest at each shift with `5*r+1 <= n`, where `r` is its
actual escape count. The sharper cycle theorem excludes cycles there.
Thus every shift of a global counterexample either has `n < 5*r+1` or
has this complete actual obstructing forest. This extracts geometric
data from the original tuple; it does not prove that those data supply
sufficient charge.

Verification: one definition and seven theorems; 15,307 full build jobs;
4,682 complete audits (4,678 standard-only, four axiom-free); 132,767
passing forest tests, including 58 new cases over all candidate shifts
in subbinary valid-gap models. The tests check complete coverage,
affine seeds, collision cuts, genuine longest endpoints, strict charge
failure and cycle rejection. Next retain exact endpoint sets when
doubling is injective. Conjecture 1 and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after every verified
milestone.

**2026-09-09 — exact genuine endpoint sets in obstructing forests.**
`InjectiveObstructingForest.lean` strengthens acyclic subbinary forest
extraction whenever doubling is injective on the tuple. The forest is
indexed by precisely the true escapes: no extra collision cut is needed.
It retains all coordinate and endpoint identities, all affine seeds,
positive chain lengths summing to `n`, genuine endpoints at every arm,
and strict bounded-corner charge failure at every arm, including short
positive arms. This implies the previous longest-arm obstruction.

Original global and exact-stratum counterexamples with injective
doubling supply this exact forest at every shift with `5*r+1 <= n`.
Odd moduli supply injectivity automatically. In the original G1 setting,
failed half descent supplies injectivity, so parent dimension `n+1`
and `5*r <= n` give the same exact forest without an added injectivity
assumption. The general collision case from the preceding milestone
remains available.

Verification: one definition and seven theorems; 15,308 full build jobs;
4,690 complete audits (4,686 standard-only, four axiom-free); 132,823
passing forest tests, including 56 new cases over every candidate shift
in odd subbinary valid-gap models. Tests check exact endpoint sets,
coverage, affine identities and every-arm charge failure. Next compare
the union of genuine exterior intervals with the actual set removed by
collision profiles, rather than only its bounded-corner upper bound.
Arbitrary sufficiently charged-family extraction remains unproved.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and
push both repositories after every verified milestone.

**2026-09-09 — actual collision loss and joint genuine exterior intervals.**
`CollisionLossPacking.lean` counts the union of the lower rectangles
from actual collision profiles, retaining overlaps. This loss is at
most the exact bounded corner and at most the sum of profile volumes.
In a sufficiently wide valid forest the rectangles are disjoint, so
loss equals that explicit volume sum. At arbitrary positive arm lengths,
every avoided set satisfies `2^n + |F| <= |G| + loss`.

For a subbinary valid forest, any selected genuine arms with
`2*n+1 <= 2^L` and `4 <= L` supply their strict eighth-width exterior
intervals as an avoided union. The union counts common residues once.
If it pays the actual loss, binary size follows. The single-arm version
likewise needs to pay only actual loss, not the entire coefficient
corner. Every subbinary forest must have exterior-union size strictly
smaller than its actual loss.

Verification: two definitions and ten theorems; 15,309 full build jobs;
4,702 complete audits (4,698 standard-only, four axiom-free); 132,847
passing forest tests, including 24 new cases. Actual valid three-arm
models have interval sizes 4, collision loss 8 and union size 12: the
joint charge succeeds while each single-arm charge fails. Further tests
cover shared exterior residues, exact collision counts and the necessary
subbinary premise for boundary exclusion. Next split actual loss and
exterior charge by parity. Arbitrary sufficiently charged-family
extraction remains unproved. Conjecture 1 and unrestricted G1/G2/G3
remain OPEN, 0/3. Continue and push both repositories after every
verified milestone.

**2026-09-09 — separate parity charges against actual collision loss.**
`ParityCollisionLoss.lean` partitions actual collision loss by the parity
of each removed point's group value. Every subbinary valid forest in
an even cyclic group has an odd seed, extracted from validity without
a failed half-descent assumption. Its binary box therefore splits
equally by parity. Each avoided set satisfies
`2^n + 2*|F_v| <= N + 2*loss_v` separately for both parity classes.

Selected genuine wide arms supply their actual exterior intervals in
each class. Paying the loss in either parity already forces binary
size, even if total exterior charge fails. Conversely, every subbinary
forest has `|F_v| < loss_v` for both classes. At modulus `2^(s+1)*q`,
`q > 0`, each class obeys the sharper rounded deficit
`2^s + |F_v| <= loss_v`. All short companion arms and overlaps remain.

Verification: one definition and seven theorems; 15,310 full build jobs;
4,710 complete audits (4,706 standard-only, four axiom-free); 132,885
passing forest tests, including 38 new cases. Actual valid models have
an even exterior interval of size 4, total collision loss 8 and even
loss 4: parity charge succeeds while total selected charge fails.
Other tests check each rounded stratum deficit and all-even valid
forests above binary size. Next prove the collision loss equals the
exact number of box points lost when forming the image, in every
chosen target set. Arbitrary sufficiently charged-family extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN,
0/3. Continue and push both repositories after every verified milestone.

**2026-09-09 — collision loss is the exact box-image deficit.**
`ExactCollisionLoss.lean` proves `|box image| + loss = 2^n` for every
complete actual valid forest with positive lengths, including short
arms and overlapping profile rectangles. Every removed point has a
strictly heavier point in the same sum fibre. A maximum-weight point
therefore survives in each fibre, and the retained map is injective.
It represents exactly the original box image.

The same identity holds inside any target predicate: target image size
plus removed points mapping there equals the original target-domain
size. With an odd seed in an even modulus, each parity image plus its
actual parity loss is exactly half the binary box. No wide-forest
hypothesis is needed for these identities.

Verification: six theorems; 15,311 full build jobs; 4,716 complete audits
(4,712 standard-only, four axiom-free); 132,922 passing forest tests,
including 37 new cases. The valid tuple `(2,3,5,9)` modulo 12 has
three-point sum fibres: its profile volumes total 8, their overlapping
union has size 6, and its box image has size 10, giving `10+6=16`.
Tests also check exact counts in several target predicates and each
parity, plus maximum-weight representatives in actual fibres.
Next bound larger fibres through their forced total-weight spacing as
box diameter grows. Arbitrary sufficiently charged-family extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN,
0/3. Continue and push both repositories after every verified milestone.

**2026-09-09 — total-weight spacing bounds actual box fibres.**
`ForestFibreSpacing.lean` proves that two colliding points in a complete
actual valid forest have total weights separated by at least `D+1-n`,
where `D = sum(2^L-1)` is the full box diameter. Complete coverage gives
`D >= n`, so this spacing is positive. Every sum fibre has at most
`D/(D+1-n)+1` points, and its actual cardinality `c` satisfies
`(c-1)*(D+1-n) <= D`.

If `n <= k*(D+1-n)`, every fibre has at most `k+1` points. Conversely,
a fibre with at least `r >= 2` points forces
`(r-2)*D+(r-1) <= (r-1)*n`. Four-point fibres therefore require
`2*D+3 <= 3*n`. These bounds interpolate below the existing
`D >= 2*n-1` threshold for two-point fibres and retain all short arms.

Verification: five theorems; 15,312 full build jobs; 4,721 complete
audits (4,717 standard-only, four axiom-free); 132,956 passing forest
tests, including 34 new cases. Tests exhaust all valid normalized
four-coordinate sets at moduli 12 through 20, their translations and
available actual chains, plus the three-point-fibre example and varied
valid-gap profiles. Next identify summed profile volumes with the
number of collision pairs, explaining their excess over union loss
when rectangles overlap. Arbitrary sufficiently charged-family
extraction remains unproved. Conjecture 1 and unrestricted G1/G2/G3
remain OPEN, 0/3. Continue and push both repositories after every
verified milestone.

**2026-09-09 — profile volumes count actual collision pairs.**
`ProfileCollisionPairs.lean` proves a bijection between points in actual
profile lower rectangles, counted with their profile labels, and pairs
of equal-sum box points ordered from heavier to lighter. A profile and
lower point determine a unique heavier partner; every ordered collision
reconstructs its actual small profile. Thus summed profile volumes equal
the number of ordered collision pairs, without a wide-forest premise.

This explains the difference from exact union loss: an overlapping
lower point contributes one pair for each heavier partner, while the
removed union counts that point once. For the valid modulo-12 example,
profile volume and pair count are 8, while union loss is 6. Both actual
coordinates and all short-arm geometry are retained.

Verification: one definition and three theorems; 15,313 full build jobs;
4,725 complete audits (4,721 standard-only, four axiom-free); 132,994
passing forest tests, including 38 new cases. Tests check both directions
of the bijection, multiple-point fibres, overlap, translation, scaling
and actual chain regrouping. Next identify complete forest boxes with
the original shifted binary subset cube, so actual collision loss can
be preserved exactly as chains change. Then charge that intrinsic loss
using actual zero-sum cycles. Arbitrary sufficiently charged-family
extraction remains unproved. Conjecture 1 and unrestricted G1/G2/G3
remain OPEN, 0/3. Continue and push both repositories after every
verified milestone.

**2026-09-09 — intrinsic subset-cube collision loss.**
`ForestSubsetCube.lean` identifies each complete affine chain forest box
with the original shifted binary subset cube by an explicit sum-preserving
bijection. This correspondence needs neither validity nor positive arm
lengths, and preserves every fibre multiplicity. For positive complete
forests of a valid tuple, the exact profile-union loss therefore equals
`tupleBinaryCollisionLoss g b`: two to the tuple dimension minus the
number of distinct subset sums after the fixed shift. Actual collision
loss is unchanged when those same coordinates are regrouped into chains.

Verification: two definitions and six theorems; 15,314 full build jobs;
4,733 complete audits (4,729 standard-only, four axiom-free); 133,055
passing forest tests, including 61 new cases. Tests recover each binary
subset from its forest point and compare complete fibre multiplicities,
including zero-length arms, coordinate permutations, overlapping short
profiles, scaling, translation and multiple valid chain regroupings.
Next charge nonempty zero-sum coordinate sets and actual affine cycles
against this fixed loss during chain continuation. Arbitrary sufficiently
charged-family extraction remains unproved. Conjecture 1 and unrestricted
G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories after every
verified milestone.

**2026-09-09 — actual cycles force intrinsic collision loss.**
`CycleIntrinsicLoss.lean` proves that a nonempty zero-sum set C of
shifted coordinates in a valid tuple forces intrinsic loss at least
`2^(n-C.card)`. In the singleton forest, its indicator complement is
an actual collision profile with precisely that lower-rectangle volume;
the removed union contains that rectangle. The complete-forest invariance
transfers this bound to the tuple's fixed intrinsic loss.

Every embedded affine doubling cycle of size c supplies such a set.
Consequently, intrinsic loss at most `2^k` forces `n <= c+k` for every
actual cycle. This binds a continued chain's extracted cycle to the same
loss budget, independently of how the remaining coordinates are grouped.

Verification: three theorems; 15,315 full build jobs; 4,736 complete
audits (4,732 standard-only, four axiom-free); 133,115 passing forest
tests, including 60 new cases. Tests verify disjoint colliding subset
faces for every nonempty zero-sum set in translated valid short examples,
and sharp loss equality for actual affine gap cycles. Next combine
intrinsic charge, genuine-endpoint packing and maximal chain continuation
to close a larger arbitrary-endpoint chain class. Arbitrary sufficiently
charged-chain extraction remains unproved. Conjecture 1 and unrestricted
G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories after every
verified milestone.

**2026-09-09 — arbitrary-endpoint intrinsic chain continuation.**
`IntrinsicChainContinuation.lean` closes the original global bound,
every exact-stratum bound and direct G3 obstruction for any actual
chain of length m satisfying `m >= 4`, `2*n+1 <= 2^m`, and
`tupleBinaryCollisionLoss g b <= 2^(m-3)`. Its endpoint and every other
coordinate are arbitrary. Completing a genuine chain by singletons
preserves intrinsic loss, so its exterior interval forces binary size.
Otherwise maximal actual continuation rejoins internally. The cycle-loss
bound and logarithmic incoming tail force a half-sized cycle below binary
modulus; the smaller-cycle case contradicts the exponential-deficit bound.

The condition can be much weaker than the previous rectangular charge.
The valid dimension-18 gap tuple at modulus `2^18-16` has intrinsic loss
16, paid by a length-7 prefix; the old `n*2^(n-m)` charge is 36,864.
This closes a broader conditional chain class, but does not extract a
charged chain from an arbitrary critical tuple.

Verification: eight theorems; 15,316 full build jobs; 4,744 complete
audits (4,740 standard-only, four axiom-free); 133,238 passing forest
tests, including 123 new cases. Tests exhaust bounded deficit arithmetic,
continue actual affine gap chains, check genuine endpoints and verify
the strict dimension-18 improvement. Next preserve and charge intrinsic
loss separately in residue predicates, especially parity, to use charge
concentrated in one class. Arbitrary sufficiently charged-chain extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after every verified milestone.

**2026-09-09 — intrinsic loss within residue predicates and parity.**
`IntrinsicFibreLoss.lean` defines exact loss inside any target predicate
as its binary subset-point count minus its distinct image count. Image
and loss recover that point count; losses for a predicate and its
complement add to total intrinsic loss, even without tuple validity.
The complete forest/subset bijection preserves every filtered point
count. Actual removed-profile loss in each predicate therefore equals
this intrinsic quantity for every positive complete valid forest.

The parity specialization is invariant under chain regrouping without
an even-modulus or width premise. At nonzero even modulus, one odd
shifted coordinate balances the subset cube: twice the parity image
plus twice its intrinsic loss equals `2^n`. Subbinary validity supplies
such an odd coordinate at every shift, without a half-deletion premise.

Verification: two definitions and nine theorems; 15,317 full build jobs;
4,755 complete audits (4,751 standard-only, four axiom-free); 133,316
passing forest tests, including 78 new cases. Tests cover arbitrary
target predicates, empty and invalid tuples, odd moduli, parity balance,
overlapping valid short profiles and complete chain regrouping. Next
count zero-sum subset faces in each parity class and charge actual
cycles against those invariant losses. Arbitrary sufficiently charged-chain
extraction remains unproved. Conjecture 1 and unrestricted G1/G2/G3
remain OPEN, 0/3. Continue and push both repositories after every
verified milestone.

**2026-09-09 — zero-sum faces charge both intrinsic parity losses.**
`ZeroSumFaceLoss.lean` proves a general discarded-point inequality:
if every domain point has a retained representative with the same image,
removed points lower-bound collision loss inside every target predicate.
Retained injectivity is unnecessary. For any tuple, subsets disjoint from
a nonempty zero-sum coordinate set C can be removed, since adjoining C
preserves their sum. A complement embedding identifies this lost face
with the entire complementary subset cube. Thus loss is at least
`2^(n-C.card)` without the validity premise used in the earlier profile proof.

At even nonzero modulus, an odd coordinate outside C divides that face
equally between parity classes: each intrinsic parity loss pays half
its size. Every actual affine cycle in a subbinary valid tuple consists
of even shifted values, so the automatically supplied odd coordinate
lies outside the cycle. Consequently `2^(n-c) <= 2*parityLoss_v` in each
class, and a parity budget `2^k` forces `n <= c+k+1`.

Verification: seven theorems; 15,318 full build jobs; 4,762 complete
audits (4,758 standard-only, four axiom-free); 133,374 passing forest
tests, including 58 new cases. Tests exhaust small finite maps, invalid
and valid zero-sum tuples, arbitrary target predicates, sharp actual
affine cycle examples, and the need for an odd complementary coordinate.
Next continue even-seed chains using intrinsic even loss alone; their
genuine exterior intervals lie entirely in that class. Arbitrary
sufficiently charged-chain extraction remains unproved. Conjecture 1
and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both
repositories after every verified milestone.

**2026-09-09 — even-seed continuation pays intrinsic even loss alone.**
`EvenIntrinsicChainContinuation.lean` closes the original global bound,
every positive exact-stratum bound and direct G3 obstruction for actual
even-seed chains at even modulus satisfying `m >= 4`, `2*n+1 <= 2^m`,
and `tupleBinaryParityLoss g b true <= 2^(m-3)`. Endpoints and remaining
coordinates are arbitrary. The entire genuine exterior interval is even,
so only intrinsic even loss must be paid. Maximal continuation preserves
that loss and seed parity. The extracted cycle leaves at most m-2
outsiders; sharper exponential-tail arithmetic still forces a half-sized
cycle below binary modulus. The rejoin helper accepts either parity class.

This improves the total-loss condition inside the subbinary regime.
For the valid dimension-18 gap tuple at modulus `2^18-16`, the chain
starting with seed 2 needs only length 6: even loss is 8 and fits its
interval, while total loss is 16 and fails the preceding criterion.
The even-modulus assumption is explicit; this is not a new odd-stratum
claim or an extraction of charged chains from arbitrary critical tuples.

Verification: eleven theorems; 15,319 full build jobs; 4,773 complete
audits (4,769 standard-only, four axiom-free); 133,512 passing forest
tests, including 138 new cases. Tests exhaust bounded sharper deficit
arithmetic, verify even multiples and genuine intervals, continue actual
affine gap chains, and check the strict dimension-18 gain. Next use
alternating interval points to charge either parity for odd seeds and
the even class for arbitrary seeds. Arbitrary charged-chain extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after every verified milestone.

**2026-09-09 — arbitrary-seed continuation from alternating parity charge.**
`ParityIntrinsicChainContinuation.lean` finds a sixteenth-width arithmetic
progression in each wide exterior interval: even coefficients give even
residues for any seed; odd coefficients give odd residues for odd seeds.
Actual axis injectivity makes these points distinct. Thus an actual chain
at even modulus closes the original global bound, every positive
exact-stratum bound and direct G3 obstruction when `m >= 4`,
`2*n+1 <= 2^m`, and its chosen intrinsic parity loss is at most `2^(m-4)`.
The chosen class may be even for any seed, or either class for an odd seed.

Endpoints and remaining coordinates are arbitrary. Maximal continuation
preserves the seed and intrinsic loss, then uses the generalized parity
rejoin theorem and an actual cycle. The preceding eighth-width allowance
for even seeds and even charge remains available. A valid dimension-4
example at modulus 14 attains the new allowance in either parity class
with odd seed 1 and chain length 4.

Verification: nine theorems; 15,320 full build jobs; 4,782 complete audits
(4,778 standard-only, four axiom-free); 133,585 passing forest tests,
including 73 new cases. Tests check alternating actual progressions,
parity conditions, genuine forests, arbitrary-start affine continuation
and both minimum-length parity choices. Next derive exact intrinsic loss
identities under coordinate insertion and deletion, retaining actual
subset-image overlaps for descent. Arbitrary charged-chain extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after every verified milestone.

**2026-09-09 — exact intrinsic loss under coordinate insertion and deletion.**
`SubsetLossRecurrence.lean` defines subset-sum image and exact loss on
an actual finite coordinate set. Inserting a fresh coordinate a adds
precisely the old image translated by x(a). Consequently the new loss
is twice the old loss plus the cardinality of the actual intersection
of those two images. This identity holds in every additive commutative
group, without validity or finiteness of the group.

On all shifted tuple coordinates these definitions equal the intrinsic
image and loss. Deleting any chosen coordinate therefore gives the exact
inverse recurrence, retaining its shifted value and the actual overlap.
Repeated insertion also proves that enlarging S to T multiplies existing
loss by at least `2^(T.card-S.card)`. These are identities and bounds for
actual coordinate deletion, not independent supplied loss budgets.

Verification: two definitions and seven theorems; 15,321 full build jobs;
4,791 complete audits (4,787 standard-only, four axiom-free); 133,642
passing forest tests, including 57 new cases. Tests exhaust small integer
and cyclic coordinate sets, all insertions and weighted growth, finite
product groups, and every deletion in valid shifted gap examples. Next
refine the recurrence inside target predicates and parity classes: odd
coordinate insertion exchanges the two old parity classes, while even
insertion preserves them. This connects intrinsic loss more directly
to descent. Arbitrary charged-chain extraction remains unproved.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and
push both repositories after every verified milestone.

**2026-09-09 — exact coordinate deletion inside intrinsic parity classes.**
`SubsetFibreLossRecurrence.lean` refines insertion and deletion inside
any target predicate. The new loss equals the old loss in the target,
the old loss in its coordinate-shifted target, and the actual translated
image overlap inside that target. Predicate and complement losses add
to total loss; the finite-coordinate definitions agree with the intrinsic
full-tuple definitions.

At even nonzero modulus, an even inserted coordinate preserves parity:
the new loss in each class is twice that class's old loss plus overlap.
An odd coordinate exchanges classes, so each new parity loss equals
the entire old collision loss plus its own overlap. The actual deletion
identities retain each shifted coordinate. In particular, deleting any
odd shifted coordinate leaves total loss bounded by either original
parity loss. No tuple-validity assumption is needed for these identities.

Verification: one definition and twelve theorems; 15,322 full build jobs;
4,804 complete audits (4,800 standard-only, four axiom-free); 133,704
passing forest tests, including 62 new cases. Tests exhaust small target
recurrences, predicate complements, odd and even deletions from valid
shifted tuples, invalid tuples with unbalanced old cubes, and the need
for even modulus in parity exchange. Next use exact loss growth and odd
deletion to bound binary collision support and force injective smaller
coordinate faces. Arbitrary charged-chain extraction remains unproved.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and
push both repositories after every verified milestone.

**2026-09-09 — intrinsic loss bounds binary collision support.**
`IntrinsicCollisionSupport.lean` proves that every equality between two
distinct shifted subset sums forces intrinsic loss at least
`2^(n - |U symmetric-difference V|)`. Common coordinates cancel, so the
support bound measures precisely the coordinates where the subsets
vary. Equivalently, `n <= support + floor(log_2(loss))`.

More generally, loss below `2^(|T|-|S|)` makes all subset sums on any
actual coordinate face `S` of `T` distinct. Zero loss is equivalent to
this injectivity. After deleting an odd shifted coordinate at even
nonzero modulus, either original parity loss supplies the same strict
budget for every remaining face. None of these results assumes tuple
validity.

Verification: six theorems; 15,323 full build jobs; 4,810 complete audits
(4,806 standard-only, four axiom-free); 133,777 passing forest tests,
including 73 new cases. Tests cover every small binary collision, common
coordinates, injective faces, sharp valid gap-cycle examples, odd
coordinate deletion, and failure at the non-strict budget boundary.
Next combine three pairwise support bounds to exclude triple fibres
under sufficiently small intrinsic loss, then count actual profiles
without a wide-diameter assumption. Arbitrary charged-chain extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN,
0/3. Continue and push both repositories after every verified milestone.

**2026-09-09 — small intrinsic loss excludes triple fibres and profile overlap.**
`SmallIntrinsicLossFibres.lean` sums three pairwise binary collision
support bounds. Each coordinate contributes at most two to the three
distances, so any three distinct subsets of equal shifted sum force
`n <= 3*floor(log_2(loss))`. Consequently, when this inequality fails,
every subset-sum fibre and every complete forest box fibre has at most
two points.

The same condition makes the actual profile lower rectangles pairwise
disjoint: a shared lower point and its two distinct heavier partners
would give a triple fibre. Their union cardinality therefore equals
the sum of their volumes, without a wide-diameter assumption. For a
valid positive-arm forest this sum equals intrinsic tuple loss. The
fibre and disjointness results themselves need no tuple validity.

Verification: seven theorems; 15,324 full build jobs; 4,817 complete audits
(4,813 standard-only, four axiom-free); 133,831 passing forest tests,
including 54 new cases. Tests exhaust small support triples and fibres,
check actual valid gap families in several regroupings including all
singleton arms, retain the valid triple-fibre overlap example modulo
12, and show the strict small-loss condition is sufficient rather than
necessary. Next count coordinate disagreements over arbitrary fibres
to obtain a general quantitative size bound. Arbitrary charged-chain
extraction remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after each verified milestone.

**2026-09-09 — arbitrary fibre cardinality from intrinsic loss.**
`IntrinsicFibreCardBound.lean` counts coordinate disagreements across
an arbitrary family of binary subsets. If its size is `m`, the ordered
support sum is at most `n*m^2/2`. Combining this with each collision's
support lower bound gives `(m-2)*n <= 2*(m-1)*k`, where
`k = floor(log_2(intrinsic loss))`, for every shifted subset-sum fibre.
Subtractions are natural. No tuple-validity assumption is needed.

When `2*k < n`, solving the inequality gives the explicit bound
`m <= floor(2*(n-k)/(n-2*k))`. Every complete actual forest encoding
inherits the same bound without a wide-diameter premise. This covers
a broader loss regime than the previous two-point theorem; actual
three-point fibres can occur here. The stronger earlier conclusion
under `3*k < n` remains available.

Verification: seven theorems; 15,325 full build jobs; 4,824 complete audits
(4,820 standard-only, four axiom-free); 133,888 passing forest tests,
including 57 new cases. Tests exhaust small binary families and sum
fibres, attain the coordinate bound with a balanced four-word family,
construct actual triple fibres in the broader quotient regime, check
valid gap families under regrouping, and retain the positive-denominator
boundary. Next express summed profile volume by exact fibre moments and
use the cardinality bound to control overlap. Arbitrary charged-chain
extraction remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after each verified milestone.

**2026-09-09 — exact profile fibre moments and overlap bounds.**
`ProfileFibreMoments.lean` proves that doubled summed actual profile
volume is `sum r*(r-1)` over nonempty sum fibres, while intrinsic loss
is `sum (r-1)`. The generic counting proof orients finite pairs by an
injective weight; validity supplies weight injectivity on each forest
fibre. The loss identity itself needs no tuple validity.

The profile moment also equals the moment of the original shifted
subset-sum fibres. Thus complete forest regrouping preserves summed
profile volume as well as intrinsic loss, including when rectangles
overlap. A uniform fibre cap `M` gives `2*volume <= M*intrinsic loss`.
The earlier intrinsic quotient bound supplies this cap when twice the
loss exponent is below dimension, without a wide-diameter premise.

Verification: nine theorems; 15,326 full build jobs; 4,833 complete audits
(4,829 standard-only, four axiom-free); 133,948 passing forest tests,
including 60 new cases. Tests exhaust small finite maps with weights
injective only within fibres, attain the cap bound, check actual valid
short forests with overlap, preserve moments across regroupings, and
retain a failure example without injective weights. Next characterize
zero profile overcounting exactly by absence of triple fibres and count
the excess caused by larger fibres. Arbitrary charged-chain extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after each verified milestone.

**2026-09-09 — exact profile overlap criterion and excess.**
`ExactProfileOverlap.lean` proves
`2*volume = 2*intrinsic loss + sum (r-1)*(r-2)` over nonempty forest
fibres. Thus summed profile volume equals intrinsic loss exactly when
every fibre has at most two points. Actual profile rectangles are
pairwise disjoint under precisely the same condition. These equivalences
require validity, but no small-loss or wide-diameter assumption.

The forward geometric implication needs only a two-point fibre cap and
diameter at least dimension, without validity. Every fibre with at least
three points contributes at least one to `volume - intrinsic loss`, so
the number of such fibres is bounded by the exact overcounting. Together
with the intrinsic moment formula, the criterion is preserved under
regrouping of the original tuple.

Verification: five theorems; 15,327 full build jobs; 4,838 complete audits
(4,834 standard-only, four axiom-free); 134,007 passing forest tests,
including 59 new cases. Tests check both directions on actual valid
short forests, exact triple-fibre excess, disjoint gap families outside
the old sufficient condition, the generic implication without validity,
and an invalid tuple showing why validity is needed for the converse.
Next cancel common coordinates and decompose binary collisions into
dyadic contributions from their disjoint relation cores. Arbitrary
charged-chain extraction remains unproved. Conjecture 1 and unrestricted
G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories after each
verified milestone.

**2026-09-09 — exact binary collision decomposition into disjoint cores.**
`BinaryCollisionCores.lean` cancels the common coordinates of every
oriented binary collision. Fixing its two disjoint difference sets `U,V`
leaves exactly `2^(n-|U union V|)` pairs, one for each common subset of
the remaining coordinates. Summing these charges over the actual cores
counts all equal-sum pairs oriented by strict subset cardinality, without
assuming validity.

For valid tuples, cardinality is injective within each shifted sum fibre,
so this core sum equals the summed volume of actual profiles in every
complete forest encoding. When all fibres have at most two points, the
same sum equals intrinsic loss. The earlier small-loss criterion supplies
that hypothesis without choosing an encoding. Cores retain their actual
positive and negative coordinate sets; they are not assumed to be cycles
or zero-sum sets.

Verification: two definitions and seven theorems; 15,328 full build jobs;
4,847 complete audits (4,843 standard-only, four axiom-free); 134,065
passing forest tests, including 58 new cases. Tests exhaust small pair
cores and oriented collisions, check actual valid profile volumes with
and without overlap, attain exact one-core charges in gap families, and
retain counterexamples without disjointness or validity. Next use dyadic
divisibility and charge budgets to force large actual relation cores.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — dyadic loss divisibility extracts actual relation support.**
`BinaryCoreDivisibility.lean` shows that if every core leaves at least
`k` free coordinates, its exact charge sum is divisible by `2^k`.
For valid tuples without triple fibres, failure of `2^(k+1)` to divide
intrinsic loss therefore extracts an actual core with support at least
`n-k`. In particular, odd loss forces a core using every coordinate.
Its two signed sides are retained; neither is assumed empty.

The exact dyadic sum also bounds the number of cores at each support
scale: `2^k` times the number leaving at least `k` free coordinates is
at most intrinsic loss. Total core count is at most loss. The earlier
small-loss criterion supplies the two-point fibre hypothesis when
needed. Divisibility can extract strictly larger support than the
logarithmic bound on every individual collision.

Verification: six theorems; 15,329 full build jobs; 4,853 complete audits
(4,849 standard-only, four axiom-free); 134,117 passing forest tests,
including 52 new cases. Tests cover all small actual core sums, support
scale counts, valid gap equality cases, a valid odd loss-3 example with
full signed support, and a loss-9 example beyond the small-loss condition.
Next determine uniqueness of full-support cores under injective doubling,
including odd cyclic modulus. Arbitrary charged-chain extraction remains
unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue
and push both repositories after each verified milestone.

**2026-09-09 — uniqueness of full-support binary relation cores.**
`FullSupportBinaryCore.lean` proves that twice either side's sum in a
full-support core equals the total shifted tuple sum. Under a two-point
fibre cap, the positive side's sum uniquely determines the entire core:
the negative side is its complement, and strict cardinality fixes the
orientation. This step requires no tuple validity or injective doubling.

If doubling is injective, all full-support cores have the same positive
sum and there is at most one. Combined with dyadic extraction, odd
intrinsic loss in a valid tuple without triple fibres gives a unique
full-support signed relation. The result specializes to every odd
nonzero cyclic modulus, including the small-loss sufficient condition.
The signed relation need not have an empty negative side.

Verification: seven theorems; 15,330 full build jobs; 4,860 complete audits
(4,856 standard-only, four axiom-free); 134,197 passing forest tests,
including 80 new cases. Tests exhaust small core values in odd and even
cyclic groups and integers, check actual valid shifted odd-modulus gap
families, retain the unique signed loss-3 example, and exhibit both
necessary boundaries: an even-modulus valid tuple with two full cores,
and failure without the two-point fibre cap. Next bound full cores by
the doubling fibre at even modulus and use parity of their count.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — unique full-support core at every cyclic modulus.**
`CyclicFullSupportCore.lean` injects full-support cores into solutions
of the doubled-sum equation. At any nonzero cyclic modulus, that equation
has at most two solutions; their representatives are distinguished by
the quotient of twice the representative by the modulus. Hence a
two-point subset-fibre cap permits at most two full-support cores.

Only full-support cores have odd dyadic charge. For valid tuples without
triple fibres, their count therefore has the same parity as intrinsic
loss. Odd loss forces exactly one full-support core at every nonzero
cyclic modulus, including even modulus where doubling is not injective.
The earlier small-loss criterion again supplies the fibre cap.

Verification: seven theorems; 15,331 full build jobs; 4,867 complete audits
(4,863 standard-only, four axiom-free); 134,299 passing forest tests,
including 102 new cases. Tests exhaust doubling fibres and small core
parities, check valid shifted odd/even modulus examples, include the
even-modulus odd loss-9 case, and retain the even loss-2 example with two
full cores. Next use subset complementation directly to extract full
support from odd loss without any fibre cap. Arbitrary charged-chain
extraction remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after each verified milestone.

**2026-09-09 — odd loss forces full support without a fibre cap.**
`OddLossFullSupport.lean` uses subset complementation to reflect the
actual binary image by `z -> total - z`. If no attained value is a half
of the total shifted sum, the reflection has no fixed points and the
image cardinality is even. In positive dimension, odd intrinsic loss
therefore forces an attained midpoint, without tuple validity or any
bound on fibre size.

For a valid tuple, a midpoint subset and its complement have equal sums
and different cardinalities. Orienting the larger side produces an actual
full-support binary relation core. Thus odd intrinsic loss forces full
support in every positive-dimensional valid tuple over any additive
abelian group. No cyclic or finite-group assumption is required, and no
triple-fibre exclusion is needed. This proves existence; multiple full
cores may remain in the same midpoint fibre.

Verification: six theorems; 15,332 full build jobs; 4,873 complete audits
(4,869 standard-only, four axiom-free); 134,372 passing forest tests,
including 73 new cases. Tests exhaust small reflected images, check
actual valid shifted tuples and infinite integer groups, and include a
valid loss-15 tuple with a four-point midpoint fibre and two full cores.
Next determine midpoint-count parity and uniqueness of the attained
midpoint value at cyclic modulus, while retaining possible multiplicity
of its relation cores. Arbitrary charged-chain extraction remains unproved.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push
both repositories after each verified milestone.

**2026-09-09 — exact midpoint parity and common full-core value.**
`IntrinsicMidpointParity.lean` proves that a finite involution-stable set
has the same cardinality modulo two as its fixed-point set. Applied to
subset complementation, binary image cardinality has the same parity as
the number of attained midpoint values. In positive dimension, intrinsic
loss has this same parity. No validity or fibre-size assumption is used.

At any nonzero cyclic modulus there are at most two midpoint roots, so
odd loss selects exactly one attained midpoint value. Every full-support
core has that same positive-side sum, even if there are several cores.
Complementation also proves that each midpoint fibre has even cardinality
in positive dimension. Value uniqueness is distinct from uniqueness of
a subset representation or a full-support relation.

Verification: seven theorems; 15,333 full build jobs; 4,880 complete audits
(4,876 standard-only, four axiom-free); 134,446 passing forest tests,
including 74 new cases. Tests cover small cyclic and noncyclic images,
valid shifted families, even midpoint fibres, the valid four-point fibre
with two cores but one midpoint value, and a noncyclic odd-loss example
with three attained midpoints. Next use complementary support distances
to sharpen the loss threshold specifically for midpoint fibres. Arbitrary
charged-chain extraction remains unproved. Conjecture 1 and unrestricted
G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories after each
verified milestone.

**2026-09-09 — half-exponent midpoint support bound.**
`MidpointFibreSupport.lean` proves that the distances from any subset to
a complementary pair add to the dimension. A third subset in a midpoint
fibre therefore forces `n ≤ 2 * Nat.log 2 L`. Consequently,
`2 * Nat.log 2 L < n` caps midpoint fibres at two points, without validity
or any restriction on other fibres. This improves the earlier general
fibre threshold `3 * Nat.log 2 L < n` specifically at midpoints.

Full-support cores are determined by their positive side and its
complement. A cap only on their common midpoint fibre suffices to identify
them. Hence valid tuples with odd loss and the half-exponent bound have a
unique full-support core at every nonzero cyclic modulus, or in any
additive group with injective doubling. The valid powers tuple modulo 30
at shift one has dimension five and loss seven: it meets the new threshold
and fails the old one. A separate unrestricted nine-coordinate example
has a two-point midpoint fibre while other fibres have three points.

Verification: seven theorems; 15,334 full build jobs; 4,887 complete audits
(4,883 standard-only, four axiom-free); 134,496 passing forest tests,
including 50 new cases. Next connect midpoint fibres to every actual
coordinate deletion, its translated target, and its image overlap.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — exact midpoint fibre halving under coordinate deletion.**
`MidpointDeletion.lean` proves reflection of subset fibres on every actual
finite coordinate set. For any midpoint `z` of the full shifted tuple,
deleting coordinate `a` gives equal fibre sizes at `z` and `z-(g a+b)`;
each is exactly half the full midpoint fibre size. No validity, cyclicity,
or loss bound is needed. Every attained midpoint consequently belongs to
the actual overlap of the deleted image and its translate by `g a+b`.

Under `2 * Nat.log 2 L < n`, every attained midpoint has exactly two subset
representations, so both corresponding deleted-coordinate targets have
exactly one representation, for every coordinate. At odd loss in a
nonzero cyclic group, this holds at the unique attained midpoint. The
four-point valid example outside this regime instead gives two child
representations at every deletion; halving alone does not imply uniqueness.

Verification: seven theorems; 15,335 full build jobs; 4,894 complete audits
(4,890 standard-only, four axiom-free); 134,587 passing forest tests,
including 91 new cases. Next combine losses on disjoint actual coordinate
blocks, then use the two complementary collision supports to sharpen the
midpoint threshold further. Arbitrary charged-chain extraction remains
unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue
and push both repositories after each verified milestone.

**2026-09-09 — combined loss on disjoint coordinate blocks.**
`DisjointCollisionLoss.lean` identifies the subset-sum image on disjoint
actual blocks with the addition image of the product of their two images.
Its cardinality is therefore at most the product of their cardinalities.
Writing `p=2^|S|`, `q=2^|T|`, and the respective losses as `lS,lT`, this gives
`q*lS+p*lT ≤ L(S∪T)+lS*lT`. No validity, finite ambient group, or cyclicity
is assumed.

If both blocks contain a collision, the combined loss is at least
`2^|S|+2^|T|-1`. Every coordinate outside the blocks multiplies that lower
bound by two. Independent zero-sum blocks attain the bound, including
its outside-coordinate factor; extra cross-block collisions can make it
strict. This counts both collision supports and improves on using their
individual lower bounds separately.

Verification: six theorems; 15,336 full build jobs; 4,900 complete audits
(4,896 standard-only, four axiom-free); 134,642 passing forest tests,
including 55 new cases. Next apply this product bound to the disjoint
supports of complementary midpoint collisions and minimize over their
sizes. Arbitrary charged-chain extraction remains unproved. Conjecture 1
and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both
repositories after each verified milestone.

**2026-09-09 — sharp balanced midpoint loss threshold.**
`SharpMidpointLoss.lean` applies the disjoint-block product bound to the
two complementary supports generated by a third midpoint representation.
If their sizes are `a` and `n-a`, then `2^a+2^(n-a) ≤ L+1`. Balancing the
sizes minimizes this expression. Thus a midpoint fibre with more than
two points forces `L ≥ 2^(n/2)+2^(n-n/2)-1`, with natural-number division.
This needs neither tuple validity nor cyclicity.

Below that threshold, every attained midpoint in positive dimension has
exactly two representations and both targets after every coordinate
deletion are uniquely represented. At odd cyclic loss, the attained
midpoint is unique; a valid tuple additionally has a unique full-support
core. The valid tuple `(1,2,4,13,20)` modulo 40 at shift two has loss nine,
below the new threshold eleven but beyond the earlier half-exponent
regime. Balanced independent zero-sum blocks attain the threshold with
four midpoint representations, so the unrestricted bound is sharp.

Verification: seven theorems; 15,337 full build jobs; 4,907 complete audits
(4,903 standard-only, four axiom-free); 134,709 passing forest tests,
including 67 new cases. Next characterize equality in the disjoint-block
product bound to recover structural information at the sharp threshold.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — equality structure in disjoint-block collision loss.**
`DisjointCollisionRigidity.lean` characterizes equality in the product loss
bound: it holds exactly when addition is injective on the product of the
two actual block images. If both disjoint blocks have positive loss, their
combined loss equals `2^|S|+2^|T|-1` exactly when each block has loss one
and block-value addition is injective. Every attained union value then
uniquely determines its pair of actual block image values.

These statements distinguish unique block values from unique subset
representations. Each block still has a collision. Positive loss in both
blocks is needed for the minimum characterization: extra cross-block
collisions can otherwise reach the same numerical value with one block
injective. No tuple validity, finite ambient group, or cyclicity is used.

Verification: four theorems; 15,338 full build jobs; 4,911 complete audits
(4,907 standard-only, four axiom-free); 134,771 passing forest tests,
including 62 new cases. Tests cover both equivalences on small actual
blocks, noncontiguous coordinates, independent equality examples, and
the necessity of the hypotheses. Next factor the actual subset fibres
under unique block-value addition and bound them at the minimum.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — exact product of actual subset fibres.**
`DisjointFibreProduct.lean` proves that every finite-map fibre has at most
one more point than the map's loss. When addition is injective on the
product of two disjoint actual block images, the union fibre at `u+v`
has cardinality exactly the product of the block fibre cardinalities at
`u` and `v`. Every union fibre is therefore bounded by `(lS+1)*(lT+1)`.

At minimum combined loss for two colliding blocks, both losses are one
and their image addition is injective. Every subset fibre then has at
most four points, and an actual four-point fibre exists. Thus the bound
is attained. A valid six-coordinate integer tuple
`(1,100,101,1000000,100000000,-101000000)` reaches balanced loss fifteen
with a four-point midpoint fibre. Its four subset cardinalities are
one, two, four, and five. Validity alone does not exclude this equality
structure in unrestricted additive groups.

Verification: seven theorems; 15,339 full build jobs; 4,918 complete audits
(4,914 standard-only, four axiom-free); 134,840 passing forest tests,
including 69 new cases. Next extract and balance the two actual blocks
at the sharp midpoint threshold, then recover the midpoint and deletion
fibre sizes there. Arbitrary charged-chain extraction remains unproved.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push
both repositories after each verified milestone.

**2026-09-09 — balanced actual blocks at the midpoint boundary.**
`MidpointBoundary.lean` extracts two disjoint colliding coordinate blocks
covering the tuple from any midpoint fibre larger than two. If loss
attains the sharp threshold `2^(n/2)+2^(n-n/2)-1`, their sizes differ by
at most one, each block has loss exactly one, and addition of their block
image values is injective. These are actual subsets of the original
coordinates; no tuple validity or cyclicity is assumed.

This structure caps every subset fibre at four. In positive dimension,
the large midpoint fibre has exactly four representations, and every
actual coordinate deletion leaves exactly two representations at both
corresponding targets. Independent balanced zero-sum blocks attain the
boundary. The valid six-coordinate example also attains it over the
integers and modulo one billion; that cyclic example lies above the
binary modulus and is not a counterexample to Conjecture 1.

Verification: seven theorems; 15,340 full build jobs; 4,925 complete audits
(4,921 standard-only, four axiom-free); 134,922 passing forest tests,
including 82 new cases. Next classify loss-one block fibres to identify
the unique four-point fibre and bound all remaining fibres at two.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — unique four-point fibre at the midpoint boundary.**
`LossOneFibres.lean` identifies exact finite-map loss with the sum of
nonempty fibre excesses. Loss one gives exactly one double fibre and
all remaining fibres have at most one point. Two such actual blocks
whose image values add injectively consequently have one four-point
union fibre, with all remaining fibres capped at two.

At the sharp midpoint boundary, the large midpoint is that unique
four-point fibre. No other fibre contains three or more points. This
classification uses no validity or cyclicity. The valid six-coordinate
boundary example has 36 singleton fibres, 12 double fibres, and one
four-point fibre; its ordered cardinality-oriented collision count is
18 while its image loss is 15.

Verification: six theorems; 15,341 full build jobs; 4,931 complete audits
(4,927 standard-only, four axiom-free); 134,997 passing forest tests,
including 75 new cases. Next transfer the classification to every actual
forest to prove exact profile volume `L+3` and locate all rectangle
overlaps at the midpoint value. Arbitrary charged-chain extraction remains
unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue
and push both repositories after each verified milestone.

**2026-09-09 — exact profile excess and midpoint overlap location.**
`ProfileMidpointBoundary.lean` proves that one four-point fibre with all
remaining fibres capped at two contributes exactly six to the doubled
profile excess. For a valid actual forest, profile volume is therefore
intrinsic loss plus three. Complete chain regrouping preserves the
sharp-boundary fibre classification, so every valid actual forest at a
large midpoint fibre on that boundary has this exact volume.

Every intersection of distinct actual profile rectangles evaluates to
the midpoint. This location statement needs no tuple validity; the
volume formula and unavoidable overlap do. Tests include nontrivial
chain regroupings and an irrelevant zero-length arm. The valid example
modulo 40 at shift eight has one four-point fibre and four other triple
fibres, giving excess seven; a unique four-point fibre alone is not
enough. The invalid two-block example has profile excess two, confirming
the separate role of validity in the exact volume statement.

Verification: seven theorems; 15,342 full build jobs; 4,938 complete audits
(4,934 standard-only, four axiom-free); 135,057 passing forest tests,
including 60 new cases. Next count rectangle incidences at each actual
box point via its heavier collision partners and finite weight rank.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — exact profile incidence ranks in every fibre.**
`ProfileIncidenceRanks.lean` proves that the number of actual profile
rectangles containing a box point equals the number of its heavier
collision partners. Injective weights on a finite set give precisely
the upper ranks from zero to one less than its size. Consequently, in
every valid actual forest fibre of size `r`, exactly `r-k` points lie
in at least `k` profile rectangles, using truncated natural subtraction.
This is a general incidence formula, without a midpoint or small-loss
assumption.

Tests retain actual rectangle membership, not only total volume. They
cover valid short forests, complete regroupings of gap families, and
boundary fibres with incidence ranks zero through three. Equal weights
invalidate the rank conclusion. Even injective fibre weights alone do
not replace tuple validity in the local profile correspondence: an
invalid nontrivial chain forest can miss heavier collision partners.

Verification: seven theorems; 15,343 full build jobs; 4,945 complete audits
(4,941 standard-only, four axiom-free); 135,110 passing forest tests,
including 53 new cases. Next aggregate these ranks into exact global
incidence levels and the complete boundary multiplicity pattern.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — global profile incidence distribution.**
`ProfileIncidenceDistribution.lean` sums the exact fibre ranks across all
actual box values. The number of points lying in at least `k` profile
rectangles is `Σ_z max(r_z-k,0)`. The number lying in exactly `k`
rectangles is the number of attained fibres of size greater than `k`.
The first upper level therefore counts intrinsic collision loss exactly.
These formulas hold for every valid actual forest, without a small-loss
or midpoint assumption.

At a large midpoint fibre on the sharp boundary, exactly two points
are multiply covered: one lies in two rectangles and one in three.
Exactly `L-2` points lie in one rectangle, and no point lies in four or
more. Thus the previously proved excess three is resolved into its
actual incidence levels. All counts are preserved under complete chain
regrouping, although the individual box points depend on the regrouping.

Verification: eight theorems; 15,344 full build jobs; 4,953 complete audits
(4,949 standard-only, four axiom-free); 135,170 passing forest tests,
including 60 new cases. Next use rectangle geometry and the boundary
loss bound to determine whether a pair can share both overlap points.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — singleton pair intersections at the midpoint boundary.**
`ProfileBoundaryIntersections.lean` proves that an actual rectangle
intersection with constant evaluation has at most one point when every
seed is nonzero. Two distinct points would supply adjacent points along
one coordinate interval; equal evaluation would then force that seed
to vanish. This uses the actual coordinate rectangle shape.

A zero shifted coordinate costs at least half the subset cube. From
dimension four onward the balanced midpoint threshold is below that
loss, so all shifted coordinates, and all positive-length actual chain
seeds, are nonzero. Consequently two distinct profile rectangles share
at most one point at a large midpoint fibre on the sharp boundary.
No tuple validity is used in these statements.

Verification: six theorems; 15,345 full build jobs; 4,959 complete audits
(4,955 standard-only, four axiom-free); 135,232 passing forest tests,
including 62 new cases. Tests cover coordinate rectangles, zero-seed
counterexamples, the dimension restriction, and valid boundary families.
Next combine singleton pair intersections with the exact incidence
levels to count intersecting profile pairs and triples. Arbitrary
charged-chain extraction remains unproved. Conjecture 1 and unrestricted
G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories after each
verified milestone.

**2026-09-09 — actual intersecting profile subfamilies.**
`ProfileIntersectionFamilies.lean` counts intersecting subfamilies of
at least two labelled finite sets by their unique common points when
every distinct pair has at most one common point. The count is the sum
of binomial coefficients of point incidences.

For an actual valid forest at the sharp large-midpoint boundary in
dimension at least four, this count is `choose(2,k)+choose(3,k)` for
`k >= 2`: four intersecting unordered profile pairs, a unique intersecting
triple, and no intersecting subfamily of four or more profiles. This
does not yet bound the total number of profiles; additional profiles
with no intersections are not excluded by incidence counting alone.

Verification: six theorems; 15,346 full build jobs; 4,965 complete audits
(4,961 standard-only, four axiom-free); 135,285 passing forest tests,
including 53 new cases. Tests exhaust small labelled set families and
check actual valid boundary examples and failures without the hypotheses.
Next classify the complementary collision pairs inside the two blocks
of loss one, then use them to constrain every boundary collision core.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — loss-one block collision supports.**
`LossOneBlockSupport.lean` proves that every distinct equal-sum subset
pair in a block of loss one is disjoint and covers the entire block.
Every proper coordinate face is therefore injective. The unique double
fibre consists of a complementary pair at a midpoint of the block sum.

Injective addition of disjoint block images makes every subset-sum
equality split into equalities in each block. For two blocks of loss
one, every nontrivial collision has symmetric-difference support equal
to the first block, the second block, or their full union. Consequently
one balanced coordinate partition controls all binary collision supports
at the sharp large-midpoint boundary. None of these six theorems needs
tuple validity or a chosen forest.

Verification: 15,347 full build jobs; 4,971 complete audits (4,967
standard-only, four axiom-free); 135,341 passing forest tests, including
56 new cases. Tests exhaust small loss-one tuples, verify independent
blocks and permuted valid boundary tuples, and check failures with
larger loss or noninjective block addition. Next count all disjoint
collision pairs across the two blocks and orient them using validity
to determine the exact number of binary cores. Arbitrary charged-chain
extraction remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after each verified milestone.

**2026-09-09 — exactly four boundary binary cores.**
`BoundaryCollisionCores.lean` defines the disjoint ordered equal-sum
subset pairs of an actual block, including the empty pair. A block of
loss one has exactly three: the empty pair and both orientations of its
unique complementary collision. Independent block addition makes these
pair counts multiply, giving nine pairs for two loss-one blocks.

Tuple validity makes the empty pair the only equal-cardinality pair.
Exactly one orientation of each remaining pair is a binary collision
core. Thus every valid tuple at the sharp large-midpoint boundary has
exactly four actual binary cores. This requires neither a chosen forest
nor a cyclic group. The total forest profile count remains to be linked
to this intrinsic core count.

Verification: one definition and six theorems; 15,348 full build jobs;
4,978 complete audits (4,974 standard-only, four axiom-free); 135,406
passing forest tests, including 65 new cases. Tests independently
enumerate equal-sum fibres and signed cores, verify exact block products
and validity-based orientation, and exhibit failures without the relevant
hypotheses. Next prove that actual forest profiles inject into the
available oriented collision count and determine their total number.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — exactly four actual boundary profiles.**
`BoundaryProfileCount.lean` strengthens the actual subset-box equivalence
to preserve disjointness when one of two digits is zero on each chain.
Every profile selects a canonical equal-sum pair with that separation
and strictly ordered box weights. The pairs from distinct profiles are
distinct; their reversals and the empty pair give a general bound by
the number of actual disjoint subset collisions, without tuple validity.

For a valid tuple, every complete forest therefore has at most as many
profiles as there are binary collision cores. At the sharp large-midpoint
boundary every complete forest has at most four profiles even without
validity. In dimension at least four, a valid positive complete forest
has exactly four, because its four intersecting unordered pairs exclude
three or fewer profiles. This establishes the total profile count,
including profiles not detected by intersection counting alone.

Verification: seven theorems; 15,349 full build jobs; 4,985 complete audits
(4,981 standard-only, four axiom-free); 135,489 passing forest tests,
including 83 new cases. Tests check arbitrary small forests, canonical
pair injectivity, genuine doubling-edge regroupings, valid boundary
families, and why sum preservation alone does not imply disjointness.
Next classify the incidence-three and incidence-two profile groups and
the entire intersection pattern. Arbitrary charged-chain extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after each verified milestone.

**2026-09-09 — complete boundary profile intersection pattern.**
`BoundaryProfileIncidencePattern.lean` selects the two actual multiply
covered box points, of incidences three and two. For a valid positive
complete forest in dimension at least four at the sharp large-midpoint
boundary, the two corresponding groups of profiles share exactly one
profile and together exhaust all four profiles. There are two profiles
only in the triple group and one only in the pair group.

Every pairwise intersection is determined by these two points. Thus the
profile intersection graph is a triangle with one attached edge. The
proof uses the actual incidence sets, the four-profile count, and the
singleton pair-intersection bound; it does not merely infer a graph from
the number of edges. A five-profile triangle plus disjoint edge is excluded
by the established total profile count.

Verification: five theorems; 15,350 full build jobs; 4,990 complete audits
(4,986 standard-only, four axiom-free); 135,530 passing forest tests,
including 41 new cases. Tests exhaust small dual incidence bounds,
labelled incidence patterns with private points, valid boundary examples,
and counterexamples when hypotheses are omitted. Next expose the actual
binary digits and compare box-weight order with original subset order
to refine the link between individual profiles and their binary cores.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

**2026-09-09 — explicit binary digits and fibre orientation.**
`ForestBinaryDigits.lean` exposes the actual subset-to-chain digit map,
proves it bijective and sum-preserving, and proves coordinatewise
additivity on disjoint subsets. Total box weight is the sum of the
selected original binary place weights. Its excess over subset
cardinality is bounded by the full forest diameter minus dimension.

Combined with valid forest weight spacing, these bounds prove that
box-weight order agrees exactly with original subset-cardinality order
on every equal-sum fibre of a valid positive forest. This is stronger
than equality of total ordered-pair counts and will allow the orientation
of each binary core to pass directly to its associated profile.

Verification: one definition and seven theorems; 15,351 full build jobs;
4,998 complete audits (4,994 standard-only, four axiom-free); 135,598
passing forest tests, including 68 new cases. Tests include arbitrary
coordinate permutations, zero-length arms, disjoint additivity, actual
valid doubling forests, long gap forests, and failures without validity
or equal sums. Next construct the actual core-to-profile map, prove its
surjectivity, and identify its boundary bijection. Arbitrary charged-chain
extraction remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after each verified milestone.

**2026-09-09 — actual binary-core-to-profile correspondence.**
`BinaryCoreProfileMap.lean` proves that each oriented binary core of a
valid positive complete forest determines a unique actual small profile
through its explicit digit differences. It defines that map, preserves
its coordinate equations, and proves every actual profile is reached.
The proof lifts a profile's canonical separated box pair back to disjoint
original subsets and uses the agreement of fibre orientations.

At the sharp large-midpoint boundary in dimension at least four, this
map is a bijection between the four actual binary cores and four actual
profiles. Surjectivity alone is the general statement: the valid forest
with lengths `(2,1,1)`, seeds `(10,7,2)`, and modulus 12 has two cores
mapping to one profile away from the boundary.

Verification: one definition and six theorems; 15,352 full build jobs;
5,005 complete audits (5,001 standard-only, four axiom-free); 135,657
passing forest tests, including 59 new cases. Tests check actual zero
digits, all available doubling edges in valid examples, long valid gap
forests, boundary bijections, and necessary hypotheses. Next express
each profile rectangle's cardinality as the sum of the dyadic charges
of the cores mapping to it, then apply the boundary bijection. Arbitrary
charged-chain extraction remains unproved. Conjecture 1 and unrestricted
G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories after each
verified milestone.

**2026-09-09 — individual profile rectangle core charges.**
`ProfileCoreCharges.lean` proves that cancelling common original subset
coordinates preserves each digit difference. For a fixed actual small
profile, its lower rectangle counts exactly the ordered original subset
pairs with that difference. Grouping them by their cancelled binary cores
gives the exact rectangle cardinality as a sum of complementary cube
charges. These general statements require neither tuple validity nor
positive chain lengths: profile smallness supplies the needed orientation.

At the valid sharp large-midpoint boundary in dimension at least four,
the core-to-profile bijection makes each rectangle equal to one core's
charge, `2^(n-support.card)`. Every rectangle therefore has power-of-two
cardinality. Away from the boundary, the valid `(2,1,1)` forest with seeds
`(10,7,2)` modulo 12 has a rectangle of size six, combining charges two
and four; a single-core formula would be false there.

Verification: six theorems; 15,353 full build jobs; 5,011 complete audits
(5,007 standard-only, four axiom-free); 135,757 passing forest tests,
including 100 new cases. Tests exhaust arbitrary small actual forests,
coordinate cancellation, valid regroupings, and the boundary formula.
Next determine the exact core support distribution across the two
balanced blocks and the resulting rectangle sizes. Arbitrary charged-chain
extraction remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after each verified milestone.

**2026-09-09 — exact boundary core support counts.**
`BoundaryCoreSupportCounts.lean` proves that a block with subset collision
loss one contains exactly one oriented binary core under tuple validity.
At the sharp large-midpoint boundary in dimension at least four, the
balanced disjoint blocks support one core each; the other two cores have
full support. These exhaust all four actual binary cores.

The core-to-profile correspondence then shows that every actual rectangle
has size one or one of the two balanced powers of two. The next step is
the exact multiplicity formula, including the coinciding large sizes in
even dimension. Tests verify valid boundary examples in dimensions five
through ten as well as the underlying support classification.

Verification: six theorems; 15,354 full build jobs; 5,017 complete audits
(5,013 standard-only, four axiom-free); 135,828 passing forest tests,
including 71 new cases. Arbitrary charged-chain extraction remains
unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after each verified milestone.

**2026-09-09 — exact boundary rectangle size distribution.**
`BoundaryRectangleDistribution.lean` transfers every weight multiplicity
through a finite bijection and applies the core-to-profile map. At the
valid sharp large-midpoint boundary in dimension at least four, the four
rectangle sizes are exactly `1, 1, 2^(n/2), 2^(n-n/2)`. The explicit
indicator formula counts coinciding large sizes twice in even dimension.
Exactly two rectangles are singletons and two are not.

Verification: seven theorems; 15,355 full build jobs; 5,024 complete audits
(5,020 standard-only, four axiom-free); 135,880 passing forest tests,
including 52 new cases. Reindexed valid examples in dimensions five
through ten check every size multiplicity. Invalid boundary and valid
nonboundary counterexamples test the need for the hypotheses.

Next identify where the two singleton rectangles lie in the established
triangle-plus-edge incidence pattern. Arbitrary charged-chain extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after each verified milestone.

**2026-09-09 — rectangle injectivity and boundary singleton locations.**
`ProfileRectangleInjectivity.lean` constructs the coordinate extrema of
every bounded profile rectangle and proves that the rectangle uniquely
determines its profile, without validity or profile smallness. A singleton
profile is twice its sole box point in every coordinate. A finite-family
lemma places two singleton members once at each of two covering points.

At the valid sharp large-midpoint boundary, these results place exactly
one singleton rectangle at the point of incidence three and exactly one
at the distinct point of incidence two. The central profile contains both
points and hence cannot be a singleton. Tests additionally confirm that
the pair-only leaf is the singleton at the point of incidence two.

Verification: six theorems; 15,356 full build jobs; 5,030 complete audits
(5,026 standard-only, four axiom-free); 135,923 passing forest tests,
including 43 new cases. Exhaustive bounded rectangles include zero-length
chains; actual boundary examples cover dimensions five through ten.
Next translate singleton geometry into restrictions on the original
chains in full-support binary cores. Arbitrary charged-chain extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after each verified milestone.

**2026-09-09 — whole chains in full-support boundary cores.**
`BoundaryCoreChainSeparation.lean` proves that a singleton rectangle lies
at a box corner and that singleton profiles have only endpoint
coordinates. Maximal explicit chain digits are equivalent to containing
every original coordinate of the chain. The negative subset's digit point
belongs to its actual core profile rectangle.

Whenever an actual core rectangle is a singleton, the coordinate identity
therefore puts each complete original chain on one side of that core.
At the valid sharp large-midpoint boundary, this applies to both
full-support cores: every chain is wholly positive or wholly negative
in each such core. These are statements about the supplied original
chain equivalence, including arbitrary reindexing.

Verification: six theorems; 15,357 full build jobs; 5,036 complete audits
(5,032 standard-only, four axiom-free); 136,016 passing forest tests,
including 93 new cases. Tests exhaust small disjoint pairs and digit
endpoints, valid long-chain examples, and actual boundary full-support
cores. Next combine the two full-support relations to put every chain
inside one balanced collision block. Arbitrary charged-chain extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after each verified milestone.

**2026-09-09 — boundary chains stay in balanced collision blocks.**
`BoundaryChainBlocks.lean` extends full-support chain separation to either
orientation of a complementary relation. Complementary pairs from the two
balanced blocks give two transverse full-support relations. A finite-set
argument confines any family lying on one side of each relation to a
single one of their four common parts.

Consequently, at the valid sharp large-midpoint boundary, the balanced
loss-one blocks can be chosen so that every supplied original chain lies
entirely inside one block. This conclusion retains the actual coordinate
equivalence and does not impose a bound on the number of chains.

Verification: four theorems; 15,358 full build jobs; 5,040 complete audits
(5,036 standard-only, four axiom-free); 136,076 passing forest tests,
including 60 new cases. Tests exhaust small transverse partitions and
complementary relation constructions, and check reindexed actual boundary
examples through dimension ten. Next strengthen block separation directly
from independent subset-sum images, without tuple validity or a chosen
forest. Arbitrary charged-chain extraction remains unproved. Conjecture 1
and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both
repositories after each verified milestone.

**2026-09-09 — boundary blocks exclude doubling without validity.**
`BoundaryDoublingBlocks.lean` shows that twice each coordinate of a
loss-one block is a difference of two actual subset sums from that block.
Independent addition of two block sumsets then forces any doubling edge
from that block into the other to end at zero. Reversing the product gives
the same conclusion in the other direction.

The sharp large-midpoint boundary in dimension at least four excludes
zero coordinates. Its balanced loss-one blocks therefore have no doubling
edge between them in either direction. This strengthens the previous
chain containment result: it requires neither tuple validity nor a
preselected forest and controls every actual shifted doubling edge.

Verification: five theorems; 15,359 full build jobs; 5,045 complete audits
(5,041 standard-only, four axiom-free); 136,143 passing forest tests,
including 67 new cases. Tests exhaust small loss-one difference sets and
independent sumsets. Explicitly invalid boundary examples in dimensions
five through twelve have long doubling chains and still satisfy the
conclusion; exact alternative coefficient vectors certify invalidity.
Next refine each block into its complementary collision parts and control
doubling there. Arbitrary charged-chain extraction remains unproved.
Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push
both repositories after each verified milestone.

**2026-09-09 — doubling preserves all four boundary collision parts.**
`LossOneDoublingParts.lean` rules out doubling between opposite sides of
a complementary collision in a loss-one block. Such an edge would create
a distinct equal-sum pair missing a block coordinate, contradicting full
support of every loss-one collision. A block closed under doubling thus
splits into two complementary parts that are each closed under doubling.

At the sharp large-midpoint boundary in dimension at least four, the two
balanced blocks consequently refine into four collision parts preserved
by every shifted doubling edge. Empty parts are allowed. These results
require neither tuple validity nor a chosen forest.

Verification: four theorems; 15,360 full build jobs; 5,049 complete audits
(5,045 standard-only, four axiom-free); 136,191 passing forest tests,
including 48 new cases. A new valid dimension-eight boundary family has
an actual length-two chain, rectangle sizes one, one, sixteen, sixteen,
and the proved singleton incidence pattern. Exhaustive coefficient
search verifies validity; this example prevents the false inference that
all valid boundary chains must have length one.

Next turn whole-block containment into a balanced subfamily condition on
chain lengths and a strict loss obstruction when no such subfamily
exists. Arbitrary charged-chain extraction remains unproved. Conjecture 1
and unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both
repositories after each verified milestone.

**2026-09-09 — balanced chain-length subfamily obstruction.**
`BoundaryChainLengthPartition.lean` propagates doubling closure along
every supplied positive chain without tuple validity. A block containing
whole chains has cardinality equal to the sum of their lengths. At the
sharp large-midpoint boundary in dimension at least four, some subfamily
of actual chains therefore has total length `n/2`. Every individual chain
has length at most `n-n/2`.

If no chain subfamily has the smaller balanced length, a large midpoint
fibre forces `2^(n/2)+2^(n-n/2) < loss+1`. This strict improvement requires
neither tuple validity nor cyclicity. The subfamily condition is necessary
for boundary equality; it is not sufficient by itself.

Verification: seven theorems; 15,361 full build jobs; 5,056 complete audits
(5,052 standard-only, four axiom-free); 136,274 passing forest tests,
including 83 new cases. Tests cover arbitrary coordinate reindexing,
zero-length coordinates in the general counting lemma, exhaustive small
forests with no balanced subfamily, valid nontrivial boundary forests,
and invalid boundary examples with long chains.

Next derive common-divisor and uniform-chain arithmetic obstructions from
the balanced subfamily condition. Arbitrary charged-chain extraction
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after each verified milestone.

**2026-09-09 — chain-length divisibility and odd uniform-chain obstruction.**
`BoundaryChainDivisibility.lean` proves that every common divisor of the
supplied chain lengths divides `n/2` at the sharp large-midpoint boundary.
For a common divisor `d >= 2`, the dimension is in fact divisible by `2*d`.
Failure of the half-dimension divisibility gives strict loss above the
balanced threshold.

In particular, an odd number of equal-length chains, each of length at
least two, cannot attain boundary equality. A large midpoint fibre then
forces strictly greater loss. Neither validity nor cyclicity is required.
Tests with two equal chains in a product of cyclic groups attain equality,
and valid odd-dimensional singleton-chain examples show why the lower
bound on the common length is needed.

Verification: six theorems; 15,362 full build jobs; 5,062 complete audits
(5,058 standard-only, four axiom-free); 136,311 passing forest tests,
including 37 new cases. Exhaustive small actual forests cover both uniform
and nonuniform divisibility obstructions.

Next connect the boundary blocks to cycle extraction: use internal
doubling predecessors to force distinct outside subset sums, then test
whether any valid boundary cycle can survive. Arbitrary charged-chain
extraction remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain
OPEN, 0/3. Continue and push both repositories after each verified milestone.

**2026-09-09 — outside injectivity and boundary cycle exclusion.**
`PredecessorClosedOutsideLoss.lean` gives a direct multiset proof in every
abelian group. A nonempty coordinate set with internal doubling
predecessors can expand its multiset to absorb the term-count decrease
of an equal-sum collision whose heavier side lies outside it. The result
omits an original coordinate and contradicts validity. All outside subset
sums are therefore distinct, and every disjoint block has loss zero.

At a valid sharp large-midpoint boundary in dimension at least four,
restricting such a predecessor set to either balanced block preserves
its predecessors. The other block would simultaneously have loss one
and loss zero. Thus no nonempty predecessor set survives, and no embedded
affine doubling cycle can occur. No cyclic-group assumption is needed.

Verification: five theorems; 15,363 full build jobs; 5,067 complete audits
(5,063 standard-only, four axiom-free); 136,352 passing forest tests,
including 41 new cases. Tests construct explicit omitted rivals, check
valid tuples with cycles away from the boundary, verify valid boundary
acyclicity, and give invalid cyclic boundary examples with actual cycles.

Next feed this cycle exclusion into actual forest extraction and derive
escape-count bounds at the boundary, retaining any necessary single
collision cut. Arbitrary charged-chain extraction away from this boundary
remains unproved. Conjecture 1 and unrestricted G1/G2/G3 remain OPEN, 0/3.
Continue and push both repositories after each verified milestone.

**2026-09-09 — actual boundary forests and escape density.**
`BoundaryEscapeDensity.lean` uses the boundary cycle exclusion to extract
an actual forest on all original coordinates whenever doubling is
injective. Any proposed escape set indexes the chains, and every chain
ends at its designated original coordinate. No forest is supplied as a
hypothesis in this extraction or its escape-count consequence.

Every valid positive forest at the sharp large-midpoint boundary has
binary diameter D < 2*n-1. Summing 4*L <= 2^L+4 over its chains gives
2*n+2 <= 5*r. Thus injective doubling forces 2*n+2 <= 5*|A|.
If the ambient group has at most one nonzero involution, an existing
construction cuts at most one collision and gives
2*n+2 <= 5*(|A|+1) for the exact escape set. The group hypothesis is
explicit; a valid boundary can have a doubled collision.

Verification: six theorems; 15,364 full build jobs; 5,073 complete audits
(5,069 standard-only, four axiom-free); 136,404 passing forest tests,
including 52 new cases. Tests reconstruct actual forests and endpoints,
check nontrivial chains and extra cuts, verify valid boundary examples
with doubled collisions, and exhibit invalid cyclic boundaries that
violate the escape bound without validity.

Next quantify finite ranked growth against outside collision gaps,
so the argument also constrains valid tuples away from this boundary.
Arbitrary charged-chain extraction remains unproved. Conjecture 1 and
unrestricted G1/G2/G3 remain OPEN, 0/3. Continue and push both repositories
after each verified milestone.

There is also an unconditional structural result in every dimension:
`DoublingValidity.lean` proves that validity forces a doubling permutation
to be a single cycle. A proper zero-sum component can be extended to full
tuple length by splitting an entry into two predecessors, contradicting
validity. `G1DoublingCycleRigidity.lean` then proves that every entry has
exact order `2^n-1`, and `mersenne_dvd_modulus_of_valid_doubling` forces
`2^n-1 ∣ N` for positive modulus `N`. In particular the odd-stratum bound
is proved for doubling-stable valid tuples in all dimensions, without G2.
The old G2-dependent cycle signatures remain compatibility wrappers; the
local proper-factor exact-two consumer now drops G2. Its upstream global
constructor still uses G2 elsewhere. No theorem makes arbitrary valid odd
tuples doubling-stable, and three-omission deletion is still open. This
closes a structural dependency, not a fourth roadmap package or a global
conjecture.

Verification for this milestone: the full 15,075-job build passes, and all
2,731 printed axiom lists use only `propext`, `Classical.choice`, and
`Quot.sound`. All twelve new declarations are included in the audit; no
proof placeholders or `native_decide` were introduced.

### Full global bound for affine-doubling-closed tuples

`DoublingClosure.lean` extends the permutation result to maps that can merge
coordinates. If a cyclic valid tuple is closed under `x ↦ 2*x+b` for one
constant `b`, validity forces all periodic coordinates onto one cycle.
Cyclic two-torsion permits at most one collision pair. Starting at a
coordinate with no predecessor then visits every coordinate; another
branch would create a second collision pair. Consequently the translated
tuple is a reindexed full initial segment of a doubling orbit.

`global_lower_bound_of_valid_affine_doubling_closed` reflects validity
through multiplication by the first orbit entry, transports to the fixed
super-increasing set, and applies `nmin_eq`. It proves `globalBound n ≤ N`
for this entire structural class, in every dimension and modulus valuation,
without G1, G2, G3, or a permutation assumption. This is a numerical global
lower-bound consumer, not only another local constraint. It does not prove
that arbitrary valid tuples have affine doubling closure; Conjecture 1 and
its three global inputs remain open. No new conjectural interface is added.

Verification: full build 15,080 jobs; all twelve new declarations audited;
all 2,764 printed axiom lists are standard-only, with no proof placeholders
or `native_decide`.

`DoublingClosureStrata.lean` strengthens the class result to exact order
and the full stratified threshold. The full-orbit generator has order
`2^n-2^t`, with `t < n`. That power gap divides `N`. Transporting the tuple
to the generated subgroup gives `t <= floor(log2 n)`; divisibility gives
`t <= s` when `N=2^s*q`, `q` odd. Therefore
`stratum_lower_bound_of_valid_affine_doubling_closed` proves the full
`stratumBound n s`, without any global conjectural input.

The six new declarations include direct consumers: no critical G1 tuple
in this class, the exact odd G2 threshold in every dimension, and no G3
exceptional lift in this class. Thus the remaining G1/G2/G3 counterexamples
would all have to fail affine doubling closure. This does not establish
closure for arbitrary tuples or discharge an unrestricted global gate.
Full build: 15,081 jobs. All six declarations are audited; all 2,770 printed
axiom lists are standard-only, with no proof placeholders or `native_decide`.

### Full global bound for an SI block plus an arbitrary entry

`SIExtensionBound.lean` proves
`global_lower_bound_of_valid_affine_fixed_prefix`: if `n-1` entries form a
coherent affine copy of the fixed super-increasing prefix in the full
modulus, any valid `n`-tuple containing them satisfies `globalBound n`.
The additional entry is arbitrary; the full tuple is not assumed to be
affine-doubling-closed. Reindexing, translation, and unit scaling are allowed.

A constructive Mersenne-coin lemma covers an initial interval with bounded
multisets. A descending geometric tail fills the short upper interval.
Below `globalBound n`, `n` terms from the retained prefix therefore cover
every residue except possibly `2^n-n-1`. A covered full-tuple sum gives a
competing multiset omitting the extra coordinate. The only other case
forces that coordinate to complete the fixed SI set, so `nmin_eq` applies.
The initial interval also directly proves
`not_validTuple_exceptional_of_affine_fixed_prefix`, a uniform G3 consumer.

The prefix hypothesis is in the **full modulus**. Arbitrary independent
half-modulus shifts of the prefix entries need not preserve it and remain
outside this theorem. This does not settle the unrestricted G1/G2/G3 gates;
no new conjectural input is introduced.

Verification: full build 15,082 jobs; all thirteen declarations audited;
all 2,783 printed axiom lists are standard-only, with no proof placeholders
or `native_decide`.

### Exact strata for SI-prefix extensions

`SIExtensionStrata.lean` strengthens the preceding class theorem to
`stratum_lower_bound_of_valid_affine_fixed_prefix`, in every dimension
`n>=3` and every valuation. Its explicit consumers rule out critical G1
tuples in this class and prove the full odd G2 threshold `2^n-1` for it.
Together with the previous G3 consumer, this removes coherent SI-prefix
extensions from all three residuals, without assuming full-tuple doubling
closure or introducing another global gate.

The proof extracts structure from validity: when `N<=2^n-3`, the arbitrary
extra entry must complete the fixed SI set. The extended cover includes
its upper boundary using four copies of the largest retained coin.
A second theorem shows that a valid fixed set below `2^n` requires
`N=2^n-2^t`; positive-multiple witnesses exclude every non-power gap.
The proved fixed-set minimum gives `t<=floor(log2 n)`, and odd-factor
divisibility gives `t<=s`, hence the exact stratum threshold.

This exact-stratum theorem retains its coherent full-modulus prefix
restriction. For G3, the independent half-modulus shifts are now handled
by the separate uniform theorem below. All three unrestricted global
obligations stay open.

Verification: full build 15,083 jobs; all eight declarations audited;
all 2,791 printed axiom lists are standard-only, with no proof placeholders
or `native_decide`.

### Uniform G3 exclusion for all independent SI lifts

`SILiftCover.lean` removes the independent-lift restriction for G3.
`exists_multiset_sum_of_si_lifts` proves that **every** lift of the retained
SI endpoint has a full `n`-fold sumset at `N=2*globalBound(n-1)`, uniformly
over all non-power-of-two `n>=3`. The explicit consumer
`not_validTuple_exceptional_of_si_lift_prefix` therefore excludes every
extra entry. An affine consumer permits reindexing, translation, unit
scaling, and arbitrary independent half-modulus shifts, including the
zero entry. No lift normalization or finite search is assumed.

The natural quotient-level consumer is
`not_validTuple_exceptional_of_quotient_affine_fixed_prefix`: the actual
retained prefix need only be affine SI **downstairs**. Every quotient
additive automorphism lifts upstairs by surjectivity of reduction on units,
so this statement imposes no additional compatibility on the lift bits.

Write `m=n-1`, `t=floor(log2 m)`, and `M=2^m-2^t`. In the quotient,
`m-1` terms cover every residue except possibly `2^m-m`. Two repeated
endpoint coins differ by `M` upstairs for every lift choice; this covers
both sheets except possibly `R=2^(t+1)-m-2`. A second pair, with
`2^j` repeated coins and `j=ceil(log2(m-2^t+2))`, covers that target.
Its even multiplicity cancels every lift bit, and the non-power-of-two
dimension condition supplies enough terms for ones and zero padding.

This is a uniform proof of the pattern previously observed by the Python
lift census, not another finite-instance claim. G3 remains open for
arbitrary tuples without such a lifted SI prefix. Neither the existence
of an SI endpoint tuple elsewhere nor the abstract G1 deletion output
establishes that the original tuple contains this prefix. The unrestricted
global count remains 0/3 closed.

Verification: full build 15,084 jobs; all fourteen declarations audited;
all 2,805 printed axiom lists are standard-only, with no proof placeholders
or `native_decide`. The unchanged finite census also passes through `n=13`,
including its non-covering power-of-two boundary controls.

### Full global bound for arbitrary coherent SI multipliers

`SIMultiplierBound.lean` proves
`global_lower_bound_of_valid_scaled_fixed_prefix`: a valid `n`-tuple
containing `c*(2^i-1)+b` for `i<n-1` satisfies `globalBound n`, for every
`n>=3`, positive modulus, and multiplier `c`, **including nonunits**.
The remaining entry is arbitrary, and reindexing is allowed. This removes
the unit restriction from the earlier coherent-prefix global theorem.
An explicit consumer also rules out this entire class at the G3 modulus.

The new ingredient is an index-two obstruction. Removing zero coins makes
value parity equal to coin-count parity, saving a term in the single-hole
cover. For a doubled SI prefix modulo `2M`, an even extra entry puts the
whole tuple in the order-`M` subgroup and contradicts its binary bound.
For an odd extra entry, the parity cover supplies a competing multiset
with three copies of that entry. Its sole exceptional target instead
forces affine doubling closure, already excluded at the G3 modulus.

To obtain the full numerical bound, factor any multiplier as a unit times
a divisor `d` of the modulus `d*M`. Validity of the retained prefix reflects
to the fixed set modulo `M`, forcing `M>=globalBound(n-1)`. A putative global
counterexample has `d<=2`. The unit case is proved already; the index-two
case's fixed-set power-gap classification forces exactly the exceptional
modulus just excluded. This is an unconditional global-bound consumer,
not an assumed structural extraction interface.

Scope remains explicit: arbitrary nonunit multipliers are covered for
**coherent full-modulus** prefixes. The independent-lift theorem separately
handles affine SI prefixes in the quotient, with unit scaling there. No
theorem here combines arbitrary nonunits with independent lift bits or
extracts either prefix from arbitrary tuples. The next theorem also removes
the unit restriction from the stronger exact-stratum bound. All three
unrestricted global obligations remain open.

Verification for the arbitrary-multiplier milestone: full build 15,085 jobs;
all eighteen declarations audited; all 2,823 printed axiom lists use only
the standard axioms, with no proof placeholders or `native_decide`.

### Power-gap rigidity and exact strata for arbitrary SI multipliers

`SIMultiplierStrata.lean` proves
`exists_power_gap_of_valid_scaled_fixed_prefix_lt_two_pow`: for every
`n>=3`, a valid tuple containing a coherent prefix `c*(2^i-1)+b`, `i<n-1`,
with any multiplier and arbitrary extra entry can occur below `2^n` only
at a modulus `N=2^n-2^t`, `t<n`. Reindexing is allowed. This necessary
condition is stronger than just the preceding global numerical bound;
it does not assert that the extra entry completes the scaled SI set.

Normalize the multiplier to a divisor `d` of `N=d*M`. Reflected validity
forces `M>=globalBound(n-1)`. For `n>=4`, three times that bound reaches
`2^n`, so `N<2^n` forces `d<=2`. At index one the prefix-completion cover
gives the fixed-set classification, except at the top two moduli, already
power gaps. At index two, the fixed set downstairs has a power-gap modulus,
which doubles to a power gap upstairs. Dimension three follows directly
from the preceding global bound.

`stratum_lower_bound_of_valid_scaled_fixed_prefix` combines this rigidity
with the global bound and odd-factor divisibility. These independently
bound `t` by `floor(log2 n)` and the actual valuation `s`. Explicit
consumers prove critical-G1 exclusion and the exact odd-G2 threshold for
**all** coherent SI multipliers. Together with the earlier G3 consumer,
this class is now excluded from all three residuals, without a unit
restriction or a new conjectural input.

The restriction still concerns an actual coherent prefix in the original
tuple. It does not classify arbitrary endpoints, extract a prefix from
arbitrary tuples, or combine arbitrary nonunits with independent lift bits.
Conjecture 1 and all three unrestricted gates remain open.

Verification for power-gap rigidity: full build 15,086 jobs; all nine new
declarations audited; all 2,832 printed axiom lists are standard-only, with
no proof placeholders or `native_decide`.

### Endpoint structure extraction and a shorter-prefix G3 consumer

`SIEndpointRigidity.lean` proves an actual normal-form conclusion:
`exists_unit_affine_fixed_of_valid_scaled_prefix_at_endpoint`. At `B(n)`,
`n>=4`, if a valid tuple contains a coherent SI prefix of length `n-1`
with any multiplier, then the whole tuple is **unit-affine SI**, after
reindexing. The remaining entry is not assumed to complete the prefix.
This class-level endpoint classification is uniform, not a finite census
or classification of arbitrary endpoint tuples.

The structural ingredient is now generalized in `SIMultiplierBound.lean`:
at an even half modulus `M<2^m`, validity of a doubled SI prefix plus an
extra entry forces that entry to reduce to `-1` modulo `M`. A power-gap
half modulus then gives full affine doubling closure. Below the binary
range, a full affine doubling orbit must have a unit generator, since a
proper cyclic subgroup would violate the binary bound. At the endpoint,
the previous index bound leaves only this doubled case or the unit case,
where prefix completion applies. The old doubled-prefix G3 exclusion now
uses the general extraction proof rather than duplicating its argument.

`not_validTuple_exceptional_of_valid_quotient_scaled_short_prefix` applies
this classification directly to G3. For non-power-of-two `n>=5`, it is
enough that the actual retained quotient of length `n-1` is valid and
contains **n-2** coherent SI entries under any multiplier. Classification
extracts its full unit-affine SI structure, and the existing uniform lift
cover excludes every independent upstairs lift and every extra entry.

Retained-quotient validity is an explicit hypothesis, not inferred from
upstairs validity. An abstract existence assertion for some smaller tuple
does not supply it, and arbitrary tuples need not have the shorter prefix.
The original three unrestricted gates remain open; no new gate is added.

Verification for endpoint extraction: full build 15,087 jobs; all seven
new declarations audited; all 2,839 printed axiom lists are standard-only,
with no proof placeholders or `native_decide`.

### Actual-deletion integration of the shorter-prefix consumer

`SIActualDeletion.lean` makes the remaining quotient-validity hypothesis
exact. `validTuple_deleted_half_iff_commonTouched` proves that, for a valid
tuple modulo `2M`, deleting a specified coordinate and reducing the actual
remaining entries modulo `M` gives a valid tuple **if and only if** every
half-witness touches that coordinate. The quotient equivalence is also
shown to compute the concrete reduction map.

`not_validTuple_exceptional_of_commonTouched_quotient_scaled_short_prefix`
therefore constructs the retained quotient directly from common touch in
the original tuple, then invokes endpoint extraction and the uniform G3
lift obstruction. For non-power-of-two `n>=5`, it needs `n-2` coherent SI
entries in the quotient, under any multiplier, with the commonly touched
coordinate outside that prefix. Reindexing and all upstairs lift bits are
allowed. No separate retained-quotient validity assumption is needed.

This is integration with the already-proved common-touch deletion branch,
not a larger class exclusion or a proof of the no-common-touch residual.
The equivalence confirms that replacing actual quotient validity by common
touch does not eliminate an open structural requirement. An abstract
`AdmitsValidTuple` assertion still does not identify the retained entries.
The same three unrestricted global inputs remain open; no new gate is added.

Verification for actual-deletion integration: full build 15,088 jobs;
all three new declarations audited; all 2,842 printed axiom lists are
standard-only, with no proof placeholders or `native_decide`.

### G3 quotient-collision branch excluded from actual tuple data

`SIQuotientCollision.lean` derives common touch from a collision of distinct
coordinates under half reduction: the original entries form an antipodal
pair. For non-power-of-two `n>=5`, a quotient collision involving either
coordinate outside a coherent `n-2`-entry SI prefix therefore excludes the
original tuple. The prefix multiplier may be a nonunit; the other endpoint
may lie inside or outside the prefix. The proof preserves the prefix while
moving the collision endpoint to the deleted position, constructs the
actual valid quotient, and applies endpoint extraction and the lift cover.
No common-touch or retained-quotient validity assumption is supplied.

`injective_quotient_of_valid_exceptional_unit_short_prefix` makes the new
residual precise. With a **unit** prefix multiplier, the shorter prefix is
itself injective in the quotient, so any hypothetical valid exceptional
tuple in this class has an injective full quotient. For nonunits, the
collision theorem still excludes all collisions involving an outside
coordinate; it does not exclude collisions entirely inside the prefix.
All independent upstairs lift bits are allowed. The injective-quotient
residual and the three unrestricted global inputs remain open.

An exploratory probe in the companion `unique` repository,
`scripts/g3-short-prefix-census.cpp`, tests a possible next uniform pattern.
After the proved unit-prefix quotient-collision exclusions and the existing
full-SI-prefix exclusion, all 7,080 remaining candidate pairs in non-power
dimensions `5,6,7,9,10,11,12` have a competing multiset using at most two
copies of each extra entry (prefix multiplicities are unrestricted).
Fourteen tests include independent direct multiset enumeration at `n=5`
and power-of-two controls at `n=8`, where four actual valid tuples survive.
This is finite evidence, not a proof of the uniform two-extra claim and not
an additional assumed roadmap gate. Such a uniform proof would address the
shorter unit-prefix residual without assuming common touch.

Verification for quotient-collision elimination: full build 15,089 jobs;
all four new declarations audited; all 2,846 printed axiom lists are
standard-only, with no proof placeholders or `native_decide`.

### Full global bound for an SI prefix with two arbitrary extras

`SITwoExtensionBound.lean` proves
`global_lower_bound_of_valid_affine_fixed_short_prefix`: for every `n>=5`
and every positive modulus, a valid tuple containing a coherent unit-affine
copy of the first **n-2** SI entries satisfies `globalBound n <= N`.
Both remaining entries are arbitrary. This is a full numerical global
bound for a broader class than the preceding `n-1`-prefix result, without
common touch, quotient validity, doubling closure, or a G1/G2/G3 input.

The proof localizes each extra using the one-extra multiset cover. If the
extras are close, doubling one supplies a rival; if they are far apart,
their full sum wraps into a prefix-only cover. The interval estimate is
uniform for `n>=7`, and explicit coin/triple-extra repairs handle `n=5,6`.
The finite short-prefix census is not used as a certificate or assumption.
`not_validTuple_exceptional_of_affine_fixed_short_prefix` gives the direct
G3 consequence in every relevant non-power dimension `n>=5`.

Scope: coherence is required in the **full** modulus, and the affine map
is an additive automorphism (unit scaling). This does not prove the
independent-lift cap-two pattern above or extraction of such a prefix from
arbitrary tuples. The later arbitrary-multiplier theorem below removes the
unit restriction for the numerical global bound and G3. The numerical bound
alone does not prove the stronger G1/G2 thresholds; the following milestone
now supplies that strengthening. All three unrestricted global inputs
remain open; no additional gate is introduced.

Verification for the two-extra milestone: full build 15,090 jobs; all
eighteen new declarations audited; all 2,864 printed axiom lists use only
`propext`, `Classical.choice`, and `Quot.sound`. No proof placeholders or
`native_decide` are used.

### Exact strata and full tuple extraction for the two-extra class

`SITwoExtensionStrata.lean` proves the actual `stratumBound`, not only
`globalBound`, for the coherent unit-affine `n-2`-entry prefix class in
every `n>=5`. Direct consumers exclude critical G1 tuples in this class
and give the odd G2 bound `2^n-1 <= N`. Together with the preceding G3
consumer, all three thresholds are now proved for this broader class.

The new uniform extraction theorem applies for `n>=7`, `N<=2^n-3`:
one of the two arbitrary extras must be the next SI entry, after which
the one-extra completion theorem extracts the full SI tuple. Affine
transport retains the original affine map and changes only the order;
an explicit endpoint corollary applies at `B(n)`. The interval argument's
near-wrap case is repaired by tripling the smaller extra. This is an
actual structural conclusion from validity, not an assumed classifier.

Consequently every valid member of this class below `2^n` has modulus
`2^n-2^t`. The last two binary residues already have that form; dimensions
five and six reuse the existing proved odd base theorems. No new finite
enumeration or unrestricted G2 assumption is used. The global envelope
and the actual valuation bound `t` separately, giving the exact strata.

Independent lift bits and extraction of a useful prefix from arbitrary
tuples remain unresolved. The following multiplier theorems remove the
unit restriction first for the numerical bound/G3 and then for exact strata.
This closes the exact-threshold gap for the existing two-extra class,
not an unrestricted G1/G2/G3 gate or a new roadmap package.

Verification for the two-extra exact-stratum milestone: full build 15,091
jobs; all eleven new declarations audited; all 2,875 printed axiom lists
use only `propext`, `Classical.choice`, and `Quot.sound`. No proof
placeholders or `native_decide` are introduced.

### Full two-extra global bound for arbitrary multipliers

`SITwoMultiplierBound.lean` proves
`global_lower_bound_of_valid_scaled_fixed_short_prefix`: for every `n>=5`,
a coherent prefix `c*(2^i-1)+b`, `i<n-2`, with two arbitrary extras satisfies
`globalBound n <= N`, for **every multiplier c**, including nonunits.
Its direct G3 consumer excludes the exceptional modulus for this broader
class in every relevant dimension. No unrestricted global gate is assumed.

Factoring the multiplier as a unit times a divisor `d` of `N=d*M` and
reflecting prefix validity force `d<=4` in a global counterexample. Index
two either completes the longer scaled prefix or gives a prefix-only rival.
Index three is excluded by subgroup reflection and coset-based covers.
At index four, the only remaining residue types are an even extra `x`
and an odd extra `y`. Two single-hole cover arguments force `x=2*y+4` and
`y mod M=-3`, respectively. These relations and the prefix power gap close
the whole tuple under `u -> 2*u+4`, giving the existing affine-doubling bound.
The proof is uniform; a small arithmetic exception reuses the proved odd
five-tuple bound. The residue splits modulo 2, 3, and 4 are kernel-checked.

This broadens the actual global/G3 exclusion class, not only an interface.
The following theorem supplies its exact G1/G2 strata. Neither theorem
combines arbitrary multipliers with independent lift bits or extracts a
prefix from arbitrary tuples. Those gaps and the three unrestricted global
inputs remain open; no new global gate is introduced.

Verification for the arbitrary two-extra multiplier milestone: full build
15,092 jobs; all thirty-two new declarations audited; all 2,907 printed
axiom lists use only `propext`, `Classical.choice`, and `Quot.sound`.
No proof placeholders or `native_decide` are introduced.

### Exact two-extra strata for arbitrary multipliers

`SITwoMultiplierStrata.lean` closes the remaining threshold gap for this
class: for every `n>=5`, a coherent prefix `c*(2^i-1)+b`, `i<n-2`, under
**any multiplier** satisfies the full `stratumBound`. Its direct consumers
exclude critical G1 tuples and give the exact odd G2 bound `2^n-1 <= N`.
Together with the preceding G3 consumer, all three thresholds now hold
for this class; at `n>=5` it also contains the earlier one-extra class.

The proof works in the full subbinary range `N<2^n`. For retained length
`m>=5`, a new `2^(m+2)<=5B(m)` bound justifies subgroup index at most four
in that larger range. The doubled case completes a longer scaled prefix
or has an explicit top-boundary power gap; the tripled case is excluded
by the coset covers. At index four, reflected fixed-prefix validity gives
a power gap directly, shifted by two when multiplied by four. Dimensions
five and six reuse the proved arbitrary-multiplier global bound and odd
base bounds, with no new tuple enumeration. The resulting power gap and
the global/valuation exponent bounds prove exact strata.

This is not arbitrary-tuple prefix extraction or a theorem for arbitrary
independent lifts of a quotient prefix. The full-tuple SI extraction
theorem previously proved for unit-affine shorter prefixes keeps its
stated hypotheses; it is not silently extended to every multiplier.
All three unrestricted global gates remain open. No new gate is added.

Verification for arbitrary-multiplier two-extra exact strata: full build
15,093 jobs; all twelve new declarations audited; all 2,919 printed axiom
lists use only `propext`, `Classical.choice`, and `Quot.sound`. No proof
placeholders or `native_decide` are introduced.

### Quarter offsets from every independent shorter-prefix SI entry

`SIQuarterPrefix.lean` extends the `H+1` obstruction in `SIQuarterExtra.lean`
to `H+a_j` for **every** prefix index `j<m`, without assuming upstairs
coherence. Write `m=n-2`, `M=B(n-1)`, and `H=M/2`. For `n>=5` not a power
of two, if the half quotient contains the first `m` SI entries and one
extra reduces to any `H+a_j`, the full tuple is invalid. Every prefix
lift bit, either lift of that extra, and the other extra are arbitrary.
Reindexing, quotient additive automorphisms, and translation are allowed.

The Mersenne-coin interval theorem is now uniform in every excess budget
`d`: with coins through `2^k-1`, at most `k+d` terms cover the interval
below `(d+2)*(2^k-1)` except its first greedy gap. Applied at budgets one
and zero, it gives an `m`-term quotient cover with at most two possible
holes for the enlarged prefix. Two copies of the quarter-offset extra
and two copies of its matched prefix entry form an antipodal pair.
The translated hole forces the other extra to reduce to `a_(j+1)`, an
actual collision or a full SI prefix. The low hole lies outside its
relevant interval unless `j=m-1`; in that boundary case it forces the
other extra to reduce to `a_(floor(log2(m+1))-1)`, another actual collision.
Existing proved G3 consumers exclude all these exceptions.

This closes all prefix-quarter-offset cases of the existing noncoherent G3
residual, not that entire residual or any unrestricted global gate. It
does not assert a full sumset cover with no exception, and does not prove
the finite cap-two observation: its constructed rival may use three copies
of the quarter-offset extra. No finite enumeration or new assumed gate is
used. Prefix extraction from arbitrary tuples remains open.

Verification for the all-index independent-lift quarter-offset milestone:
full build 15,095 jobs; all six new declarations audited; all 2,930 printed axiom
lists use only `propext`, `Classical.choice`, and `Quot.sound`. No proof
placeholders or `native_decide` are introduced.

### Coherent-prefix extraction from a negative-one quotient extra

`SILiftMinusOne.lean` derives, rather than assumes, upstairs coherence.
For a valid tuple of length `m+2` in `ZMod (2*M)`, with `m>=2` and any
positive `M`, suppose its actual quotient has the first `m` SI entries
and the last extra reduces to `-1`. After translating by the actual
lifted zero, the lifted negative one and lifted one must sum to `M`:
otherwise they sum to twice the lifted zero, a forbidden two-entry rival.
Any wrong lift at a later prefix coordinate would likewise sum with that
extra to twice its predecessor. Validity therefore forces the whole
prefix to use the multiplier given by the actual lifted one. No lift
coherence, unit multiplier, or endpoint classification is assumed.

The canonical affine-prefix extraction gives the full numerical
`globalBound (m+2) <= 2*M` for `m>=3` at every positive `M`, using the
already proved arbitrary-multiplier two-extra bound. The direct G3
consumer also permits quotient affine transport and reindexing. The
other extra and every initial lift bit are arbitrary; there is no finite
enumeration or unrestricted G1/G2/G3 input.

This excludes the negative-one case of the shorter-prefix residual and
provides a genuine structural extraction theorem. It does not extract a
prefix from arbitrary tuples or exclude arbitrary shorter-prefix lifts.
The unrestricted global lower bound and all three global inputs remain
open; no additional global gate is introduced.

Verification for negative-one coherence extraction: full build 15,096
jobs; all six new declarations audited; all 2,936 printed axiom lists
use only `propext`, `Classical.choice`, and `Quot.sound`. No proof
placeholders or `native_decide` are introduced.

### Quarter separation between the two independently lifted extras

`SILiftQuarterPair.lean` closes the two-extra quarter-separation application.
For any positive even half modulus `M=2H`, a valid length-`m+2` tuple with
an independently lifted length-`m` SI quotient prefix and extras differing
by `H` in that quotient satisfies `globalBound (m+2) <= 2*M`, for `m>=3`.
This is the full numerical global bound, not only an exceptional-modulus
exclusion. Quotient affine transport and reindexing are allowed, and all
lift bits are arbitrary. Direct G3 consumers are included.

Below the global threshold, `H<=2^m-2`. The two quotient extras select a
remainder in the lower half; `m-1` prefix coins represent it except at
`F=2^m-m`. Two copies of either extra differ by `M` upstairs, so either
sheet yields a full-length rival with a repeated coordinate. At the hole,
one extra has quotient `H-1` and the other `-1`; the already proved
negative-one extraction gives the global bound instead. Both holes,
either choice of extra, and the multiplicity contradiction are proved.
No finite enumeration, coherence hypothesis, or unrestricted gate is used.

Together with the earlier all-prefix quarter-offset exclusion, this
removes the remaining quarter-separation case involving the two extras
from the existing G3 shorter-prefix residual. It does not settle arbitrary
independent lifts, extract a prefix from arbitrary tuples, or close an
unrestricted global gate. No new roadmap gate is introduced.

Verification for the two-extra quarter-separation milestone: full build
15,097 jobs; all six new declarations audited; all 2,942 printed axiom
lists use only `propext`, `Classical.choice`, and `Quot.sound`. No proof
placeholders or `native_decide` are introduced.

### Binary threshold for the quarter-separated two-extra class

`SIQuarterBinary.lean` strengthens the preceding numerical bound to
`2^(m+2) <= 2*M`, for every `m>=3` and positive even half modulus `M=2H`.
The hypotheses are unchanged: an actual length-`m` unit-affine SI prefix
in the half quotient, two extras differing by `H` in that quotient, and
arbitrary independent lifts. Reindexing and quotient affine transport
are included. The explicit stratum consumer consequently proves every
`stratumBound (m+2) t <= 2*M`, excluding this class at the critical G1
threshold as well as at G3. This is a theorem for the even-modulus class,
not a new proof of arbitrary odd G2.

The one-hole quotient cover now includes the full `H<2^m` range: at its
last boundary point, two copies of the largest Mersenne coin suffice.
At the remaining negative-one hole, actual coherence is already proved.
Translate by the lifted zero and let `c` be the lifted one. Since the half
modulus is even, `c*c=1` and `c*M=M`; multiplying by `c` and adding one
turns the prefix into `1,2,...,2^(m-1)` and the negative-one extra into
`M`. The partner projects to `H`. A binary subset represents
`2^m-H-1`, copies of the order-two extra pad the length, and two copies
of either extra select the correct sheet. The resulting repeated
coordinate contradicts validity. Thus the former hole cannot survive
anywhere below the binary threshold.

This closes the stronger threshold for an existing class; it adds no
assumed global input or finite-instance requirement. The stronger binary
bound concerns separation of the TWO EXTRAS, not an extra separated from
a prefix entry. The latter all-prefix theorem retains its G3-only scope.
Other independent lifts and arbitrary prefix extraction remain open;
Conjecture 1 still has 0/3 unrestricted global gates closed.

Verification: full build 15,098 jobs; all six new declarations registered
in the axiom audit; all 2,948 printed axiom lists use only `propext`,
`Classical.choice`, and `Quot.sound`. No proof placeholders or
`native_decide` are introduced.

### Quarter-minus-one extra: a new uniform independent-lift exclusion

`SIQuarterMinusOne.lean` excludes an extra at normalized quotient value
`M/2-1`, for `M=globalBound(n-1)` and every `n>=9`. The `n-2` SI quotient
prefix has arbitrary independent lift bits; the other extra is arbitrary.
The direct G3 consumer includes reindexing and quotient affine transport,
and does not require the full dimension to be a non-power of two.

The extracted general pattern is a one-fewer-coin Mersenne cover: with
`k-1` coins through `2^k-1`, a target `x<2*(2^k-1)` can fail only when
`x+k=2^(k+1)` or `x+k+2^j=2^(k+1)` for some `0<=j<=k`.
For `m=n-2`, `P=2^m`, and `M=2*(P-d)`, four-term antipodal blocks then
cover all quotient targets except at most
`P-m-3`, `2*P-m-3-d`, and `2*P-m-3-2*d`.
Any noncoherent prefix lift supplies a three-term antipodal block whose
remaining coin budget repairs all three targets. Thus the shorter prefix
and the quarter-minus-one extra have the FULL `(m+2)`-fold upstairs sumset,
which gives a rival omitting the other extra. The coherent alternative is
excluded using the already proved full-SI extraction, not an assumed
classification. Actual lifted zero/one normalization and both sheets are
checked.

The generic theorem works for `m>=7`, dyadic `d>=4`, `2*d<=m+1`, and
`8*(m+d+1)<=2^m`; the exceptional modulus meets these inequalities by a
proved arithmetic lemma. This is a new excluded family within G3, not a
new assumed gate or a theorem for arbitrary shorter-prefix lifts. Its G3
consumer has the explicit `n>=9` scope. The following completion removes
the small-dimensional gap for this family; unrestricted G1/G2/G3 remain
open. The exploratory finite searches are not proof inputs.

Verification: full build 15,099 jobs; all 17 new declarations registered
in the axiom audit; all 2,965 printed axiom lists use only `propext`,
`Classical.choice`, and `Quot.sound`. No proof placeholders or
`native_decide` are introduced.

### Quarter-minus-one family complete in every relevant dimension

`SIQuarterMinusOneComplete.lean` extends the G3 exclusion to every
non-power full dimension `n>=5`, including the formerly open `n=7` case.
The direct consumer includes quotient affine transport, an arbitrary
other extra, and arbitrary independent prefix lifts. The `n>=9` theorem
without a non-power premise remains available as well.

The small logarithmic block is not enumerated. A new structural theorem
holds for EVERY `m>=3` at half modulus `M=2*(2^m-2)`: if the first extra
projects to `M/2-1`, validity forces the other extra to project to the
next SI entry `2^m-1`. Normalize the actual lifted zero and one. A lower-
sheet first extra would make a double equal two distinct tuple entries,
so validity selects the upper sheet. The extra and the lifted one then
form an antipodal pair with two copies of the top prefix coin. The
remaining `m`-term quotient cover misses at most `2^(m+1)-m-3`; at that
hole, equality of the full target forces the next SI entry. Reindexing
therefore exposes the already excluded full SI quotient prefix.

This closes the outstanding base of an existing G3 family using a new
general extraction pattern. It adds no assumed global gate, and does
not settle arbitrary independent lifts or Conjecture 1 (still 0/3).

Verification: full build 15,100 jobs; all five new declarations registered
in the axiom audit; all 2,970 printed axiom lists use only `propext`,
`Classical.choice`, and `Quot.sound`. No proof placeholders or
`native_decide` are introduced.

### Independent-lift midpoint extensions satisfy the binary bound

`SILiftMidpoint.lean` proves `2^n<=N` for every `n>=5` and positive
even modulus `N=2*M` when the actual half quotient contains a unit-affine
SI prefix of length `n-1` and the remaining entry is a midpoint of two
DISTINCT prefix entries. All upstairs lift bits are arbitrary. The half
modulus may be odd or even; quotient affine transport and reindexing are
included. Exact-stratum bounds and a direct critical-G1 exclusion follow.

Validity forces the downstairs midpoint relation onto opposite sheets
upstairs. The `n-2`-term quotient cover, now extended through its final
subbinary boundary, gives a full-length rival with either zero or two
copies of the extra. Its only possible hole forces the extra to -1.
The proved negative-one coherence extraction supplies `globalBound n<=N`,
whereas the midpoint equation forces `M` to divide a sum of two distinct
powers of two and hence `N<=3*2^(n-2)`. These bounds contradict each other
for every `n>=5`, closing the hole uniformly.

This is a new all-modulus binary/G1 result for a structural family, not
another isolated exceptional residue or an assumed interface. Full
`n-1`-entry SI quotient prefixes were already excluded at G3; that gate's
scope is not enlarged here. Do not shorten this theorem's prefix to
`n-2`, drop distinctness, or infer a midpoint in arbitrary tuples.
Unrestricted G1/G2/G3 and Conjecture 1 remain open (0/3); no new gate is
introduced. No finite census is a proof input.

Verification: full build 15,101 jobs; all seven new declarations registered
in the axiom audit; all 2,977 printed axiom lists use only `propext`,
`Classical.choice`, and `Quot.sound`. The existing 14 regression tests pass.
No proof placeholders or `native_decide` are introduced.

### Actual SI half deletion closes all even-modulus thresholds

`SIHalfDeletionStrata.lean` extends the formerly G3-only actual-deletion
and quotient-collision results to every positive even modulus `N=2*M`,
for every `n>=5`. If a specified actual half-deleted quotient is valid
and contains a coherent SI prefix of length `n-2` under ANY multiplier,
then `globalBound n<=N` and the exact bound for the actual valuation hold
upstairs. Original lift bits remain arbitrary; nonunit quotient scaling
is permitted. Common touch outside the prefix constructs that specific
quotient, as does a quotient collision involving an outside coordinate.
Direct numerical and critical-G1 collision consumers are included.

The mechanism is a general transfer of modulus rigidity. A subbinary
valid coherent SI-prefix extension has a power-gap modulus at which the
full fixed set is also valid. If doubling that modulus violated the next
global bound, it would have to be exactly the previous endpoint in a
non-power dimension. Actual retained-quotient endpoint extraction and
the proved SI lift cover exclude that case. Consequently, throughout
the original subbinary range, the full fixed SI set is valid at the
ORIGINAL modulus too. Its exact-stratum theorem supplies the stronger
threshold. This does not classify the original tuple as fixed or affine SI.

For a UNIT-scaled shorter quotient prefix, the entire remaining quotient
must now be injective at EVERY critical even stratum, not just G3.
The general abelian binary floor makes the prefix itself injective;
the new collision theorem excludes any collision involving its extras.
Thus this removes a full family from the global/G1 residual, with no new
assumed gate. It does not infer retained-quotient validity, common touch,
or prefix structure from arbitrary upstairs validity. Arbitrary odd G2,
other independent lifts, and unrestricted G1/G2/G3 remain open (0/3).
No finite census is an input to these proofs.

Verification: full build 15,102 jobs; all twelve new declarations registered
in the axiom audit; all 2,989 printed axiom lists use only `propext`,
`Classical.choice`, and `Quot.sound`. All 14 existing regression tests pass.
No proof placeholders or `native_decide` are introduced.

### Direct G1 descent through a large parity fibre

`G1ParityFibreDescent.lean` proves actual half-size descent for any valid
cyclic `(n+1)`-tuple whose entries, apart from one coordinate, have the same
parity. More generally any `k` same-parity embedded coordinates give a
valid `k`-tuple modulo half the original modulus: translate by a lift of
the common parity, divide even representatives by two, and reflect validity
through the doubling embedding. This works in all dimensions and positive
even moduli. It needs no SI prefix, common touch, half-witness, or criticality.

Consequently, a parity fibre with at least `n` entries already proves the
required `AdmitsValidTuple n M` conclusion. Every valid `(n+1)`-tuple at
`2*M` therefore either admits that smaller tuple or has at least two entries
in EACH parity fibre. The equivalence
`criticalThreeOmissionDeleteStep_iff_two_large_parity_fibres` restricts the
same outstanding G1 obligation to those two-large-fibre tuples.
`global_lower_bound_of_two_large_parity_threeOmissionDeleteStep` connects
this narrower residual directly to the existing global induction, still
with the same explicit G2 and G3 inputs. This is an actual deleted-coset
construction followed by a proved residual restriction, not a new gate.

Coset halving is NOT canonical reduction modulo `M`. A companion exact
regression enumerates all 6,435 length-eight compositions for
`(0,351,89,1323,1729,1209,579,1757)` modulo 2012: it is valid with one even
entry, but four explicit half-witnesses leave no common-touch coordinate,
and every canonically deleted half quotient is invalid. Deleting zero,
subtracting one, and halving instead gives a valid seven-tuple modulo 1006.
This computational guardrail is above the binary range, is not a critical
G1 counterexample, and is NOT an input to the uniform Lean proof.

No theorem here claims every subbinary valid tuple has a singleton parity
class. The unresolved G1 work remains deletion (or contradiction) for
critical three-omission tuples with both parity fibres of size at least two,
together with the previously retained restrictions. Arbitrary G2/G3 and
Conjecture 1 remain open (0/3).

Verification: full build 15,103 jobs; all nine new declarations registered
in the axiom audit; all 2,998 printed axiom lists use only `propext`,
`Classical.choice`, and `Quot.sound`. All 18 regression tests pass, including
the four new exact parity/descent guardrails. No proof placeholders or
`native_decide` are introduced.

### Independent SI lifts now give actual higher-even G1 descent

`SILiftParityDescent.lean` proves
`admitsValidTuple_half_of_subbinary_even_quotient_affine_si_prefix`:
for every `n>=5`, positive `N` divisible by four, and `N<2^n`, a valid
tuple with an actual unit-affine SI half-quotient prefix of length `n-1`
implies `AdmitsValidTuple (n-1) (N/2)`. The original lift bits, extra entry,
reindexing, and quotient translation/automorphism are arbitrary. This is
the actual deletion conclusion throughout the subbinary range, including
all higher critical even strata, not another assumed roadmap interface.

The uniform mechanism has two branches after normalization:

- A three-term recurrence defect at prefix index `j` forces the extra
  quotient value to be `1+2^j-p`, where `p=0` or `p=2^l`, `l<=n-2`.
  One-fewer-coin covering and two antipodal prefix blocks produce an
  actual full-length rival at every other value; BOTH blocks omit the extra.
- If the extra is even, parity leaves only `p=1`. For an interior defect,
  the resulting value `2^j` is a midpoint of two distinct prefix entries,
  contradicting the proved binary bound. All interior recurrences therefore
  hold, extracting a coherent actual `n-2` prefix. Its power-gap modulus
  gives a smaller valid fixed tuple at `N/2`, with arbitrary multiplier.
- If the extra is odd, all normalized entries except zero are odd.
  Deleting zero and halving that translated coset gives the smaller tuple.

The defect-localization lemma itself works for arbitrary positive half
moduli within its explicit cover bound. Evenness of the half modulus is
needed for the subsequent parity argument. The proof does not assert
that all lift bits are coherent or identify coset halving with canonical
half reduction. Exact endpoint regressions at n=5,6,7 exercise a valid
noncoherent odd-extra branch; their analogous n=8 tuple is explicitly
checked to be INVALID, preventing a spurious all-dimensional example.
These checks are not proof inputs.

The remaining G1 residual has two large parity fibres and, in strata
`v2(N)>=2`, lacks this extracted full unit-affine quotient prefix (or is
handled by another proved branch). The first even stratum, arbitrary
prefix extraction, shorter independent prefixes, G2, and G3 remain open.
No new global gate is introduced; Conjecture 1 remains open, 0/3.

Verification: full build 15,104 jobs; all eight new declarations registered
in the axiom audit; all 3,006 printed axiom lists use only `propext`,
`Classical.choice`, and `Quot.sound`. All 22 regression tests pass,
including four new lift/parity scope checks. No proof placeholders or
`native_decide` are introduced.

### First-even full-prefix lifts have a unique interior defect

`SILiftOddDefects.lean` proves
`exists_unique_short_prefix_defect_of_critical_odd_quotient_affine_si_prefix`.
For `n=m+2>=5`, odd positive `M`, and `2*M<2^n-2`, a hypothetical valid
full SI quotient-prefix extension has exactly one defect among indices
`0..m-1` relative to its own actual affine multiplier. Indices zero and
one are automatically coherent, so the defect lies in `2..m-1`.
Reindexing, quotient affine transport, and all original lift bits are
allowed. The terminal prefix index `m` and extra index `m+1` are not
claimed coherent or determined.

Each interior defect gives an extra quotient value `1+2^j-2^l`,
`1<=l<=m`: the zero and unit complement cases are excluded by the proved
midpoint bound. Two defects would equate two even sums of powers of two.
The universal subgroup bound puts each sum below `2*M`. Since `M` is odd,
their congruence is an equality of natural numbers, with no one-period
wraparound. Binary uniqueness forces the extra quotient to equal one.
The existing actual quotient-collision threshold excludes that value.
No defect is also impossible by the coherent `n-2` prefix threshold.
Thus validity EXTRACTS the unique defect; no census or open gate is used.

This does not yet close the first-even full-prefix class, arbitrary-prefix
extraction, or any unrestricted global gate. The immediate structural
target within this class is its single interior defect, with arbitrary
terminal lift and extra. The larger queue remains G1, G2, G3, 0/3 closed.

Exact regressions at n=6,7,8 show that multiple defects ARE allowed at
`N=2^n-2`; the strict critical bound cannot be dropped. Another exact
guardrail checks `(0,484,65,301,209,373,431)` modulo 502: it is valid, has
two even entries, and has no common-touch coordinate. It is above the
binary range, not a critical G1 counterexample. A two-entry minority
parity fibre alone therefore does not imply common touch.

Verification: full build 15,105 jobs; all nine new declarations registered
in the audit; all 3,015 axiom lists standard-only; all 26 exact regressions
pass. No proof placeholders or `native_decide` are introduced.

### First-even normal form and actual same-parity G1 descent

`SILiftOddNormalForm.lean` strengthens the preceding unique-defect result.
For odd positive `M`, `2*M<2^n-2`, `n=m+2>=5`, and a full SI quotient
prefix, normalize the actual lifted zero to zero and let `c` be the actual
lifted one. Validity extracts indices `2<=j<m`, `3<=l<=m`, `l!=j`, with

    g_i = c*(2^i-1) + (if i=j then M else 0),  0<=i<=m
    g_extra = c*(1+2^j-2^l)                    in ZMod (2*M).

The terminal lift is now proved coherent, and the extra is determined
UPSTAIRS, not merely in the quotient. The multiplier may be a nonunit.
No independent lift choices or coherence assumptions are hidden here.

The general mechanism is pair-sum rigidity. A forbidden pair equality
in a two-sheet quotient must lie on opposite sheets upstairs. Two such
identities with a common entry and target force a forbidden actual third
pair identity. These lemmas do not assume SI structure or criticality.
They also strengthen the near-power exclusions to every positive modulus.
Complement four propagates a defect to the lifted entry three, so cannot
be an isolated defect elsewhere. A terminal defect would have its own
dyadic complement. Odd-period non-wraparound leaves only the terminal
power for the extra; the pair triangle excludes it, including a terminal
complement index. Finally another forced pair sum determines the extra
on its actual sheet.

`admitsValidTuple_half_of_critical_odd_quotient_affine_si_prefix_same_parity`
then constructs a valid `(n-1)`-tuple modulo `M` whenever the original
lifted zero and one share parity. In the normal form every entry except
the unique defect is even, so retained-coset halving applies. Quotient
affine transport, reindexing, and arbitrary original lift bits are allowed.
This closes that first-even G1 branch, not merely an interface for it.
The opposite-parity normal-form branch, arbitrary-prefix extraction, and
unrestricted G1/G2/G3 remain open, 0/3; no new gate is introduced.

An exact regression rejects a proposed unrestricted shortcut: the valid
tuple `(0,146,221,289,451,301,321)` modulo 502 has two even entries, but
every merge `even_a+even_b-odd_anchor`, followed by retained-coset halving,
is invalid. This is above criticality and does not refute G1 or other
descent constructions. The regression checks every candidate and its
rival-count obstruction; it is not a Lean proof input.

Verification: full build 15,106 jobs; all fourteen new declarations
registered in the audit; all 3,029 axiom lists standard-only; all 27
regressions pass. No proof placeholders or `native_decide` are introduced.

### Complete first-even class and all-stratum full-prefix G1 descent

`SILiftOddComplete.lean` proves
`first_even_lower_bound_of_valid_quotient_affine_si_prefix`:

    n>=5 + M odd + valid full unit-affine SI half-quotient prefix
      -> 2^n-2 <= 2*M.

This closes the ENTIRE first-even critical full-prefix class, including
the opposite-parity normal forms left above. There is no remaining
single-defect, terminal-lift, extra, or lifted-one parity obligation for
this class. Quotient affine transport and reindexing are included, and
all original independent lift bits and extra values are allowed.

The final argument extracts uniform small rivals from the normal form,
with no parity or modulus restriction in its n>=6 algebraic part:

- If j>=3, `g_extra+g_l+g_1 = 2*g_(j-1)+g_2` is a three-term rival,
  so the defect must be at j=2.
- If l>=4, `g_extra+g_l+g_3+g_1 = 4*g_2` is a four-term rival,
  so the complement must be l=3.
- The resulting extra is `-3*c`. For n>=6,
  `g_extra+g_4+g_1 = 2*g_2+g_3` is a three-term rival.

Each removed side has distinct coordinates, and the replacement contains
an outside coordinate. A general multiset-replacement theorem turns each
identity into an actual full-length rival. For n=5, the critical range
and binary floor leave only M=9,11,13 and two possible lifted-one values;
six explicit pair identities close that base. These are exact kernel-
checked identities, not a finite census input to the general proof.

Below `2^n`, the threshold forces `M=2^(n-1)-1`. The proved fixed tuple
at this Mersenne endpoint gives actual half descent, including the valid
boundary. `admitsValidTuple_half_of_subbinary_quotient_affine_si_prefix`
combines this with higher-even descent: the full unit-affine half-quotient
prefix class now leaves G1 in ALL even strata, for every n>=5. No common
touch, criticality, half-witness, or unrestricted global gate is assumed
by this final subbinary descent theorem. This is not a claim that its
smaller tuple is a canonical deleted quotient.

The structured propagation target is now closed by the full-bound theorem
below. The remaining work is extraction from arbitrary critical tuples.
Shorter independent prefixes and unrestricted G1/G2/G3
remain open, 0/3; no new gate is added. Historical residuals above are
superseded for this full-prefix class, not additional open milestones.

Verification: full build 15,107 jobs; all twelve new declarations audited;
all 3,041 axiom lists standard-only; all 32 regressions pass. Five new scope
checks exercise the final uniform rival with unit/nonunit multipliers and
verify a valid n=5 control ABOVE criticality, where the n>=6 rival is not
available. No proof placeholders or `native_decide` are introduced.

### Full global and exact-stratum bounds for independent full quotient prefixes

`SILiftSmallBases.lean`, `SILiftStructuredDescent.lean`, and
`SILiftFullBound.lean` close the numerical bound for this entire class:

    n>=3 + N=2*M>0 + valid full unit-affine SI half-quotient prefix
      -> globalBound n <= N
      -> separately, stratumBound n s <= N whenever N=2^s*q, q odd.

The second bound is proved directly, not inferred from the weaker global
bound. The main APIs are
`global_lower_bound_of_valid_quotient_affine_si_prefix` and
`stratum_lower_bound_of_valid_quotient_affine_si_prefix`. Reindexing,
quotient affine transport, all original lift bits, and the extra are
unrestricted within the prefix hypothesis. No G1/G2/G3 premise is used.

The stronger subbinary conclusion is fixed-set validity at the original
modulus, `valid_fixed_of_valid_quotient_affine_si_prefix_lt_two_pow`.
Consequently `N=2^n-2^t`, with `t<n` and `2^t<=n`. This is a theorem
about the modulus, not an affine classification of the original tuple.

The proof is a dimension induction. In the higher-even odd-extra branch,
the actual retained odd coset, translated and halved, is valid and retains
a full SI prefix in its NEXT half quotient. The even-extra branch has an
actual coherent shorter prefix. The first-even branch has its proved
Mersenne endpoint. If doubling the child's admissible gap exceeds the
parent budget, the already proved uniform independent-lift cover produces
a contradiction. Fixed n=3,4 bases use kernel-checked `decide` on bounded
rival certificates (moduli 4,8,10); no external census is a proof input.

Thus this full unit-affine half-quotient prefix class has no remaining
global-bound, exact-even-stratum, or structured propagation obligation for
n>=3. An arbitrary even counterexample must lack such a prefix. The
nonunit quotient-prefix restriction is removed for n>=5 below. Shorter
independent prefixes, arbitrary extraction, and unrestricted G1/G2/G3
remain open; no fourth gate has been added.

Verification: full build 15,110 jobs; all eighteen new declarations audited;
all 3,059 axiom lists standard-only; all 34 regressions pass. The regressions
also check the actual child's next quotient prefix and the fixed n=4 bases.
No proof placeholders or `native_decide` were introduced.

### Full independent quotient-prefix bounds with arbitrary multipliers

`SILiftMultiplier.lean` proves the global and every exact even-stratum
bound for a full `n-1` SI half-quotient prefix under ANY multiplier,
every n>=5. Nonunit scales and arbitrary original lift bits are now
allowed simultaneously. The extra, translation, and reindexing are free.
Below `2^n`, fixed-set validity holds at the SAME modulus, hence an
admissible power gap. The main APIs are
`global_lower_bound_of_valid_quotient_scaled_si_prefix` and
`stratum_lower_bound_of_valid_quotient_scaled_si_prefix`.

The proof normalizes the quotient multiplier to a divisor d of the half
modulus `d*L`. The actual retained prefix divides to a valid tuple modulo
`2*L` whose full half quotient is the unit SI set. Its proved numerical
bound forces `d<=2` below the parent binary bound. Index one uses the unit
theorem. At index two, the child modulus is `2^r-2^t`, with `t>=1`.
The parent's terminal prefix coordinate and coordinate `t-1` then have
the SAME actual half-quotient value. This collision constructs a valid
half deletion preserving a coherent shorter quotient prefix; the existing
consumer gives original-modulus fixed validity and all stratum bounds.

No affine classification of the original lifts, independent finite census,
or unrestricted G1/G2/G3 premise is used. The nonunit full-prefix residual
is CLOSED for n>=5, not another open gate. Shorter independent prefixes
and arbitrary structural extraction remain open; Conjecture 1 and all
three unrestricted obligations stay open, 0/3.

Verification: full build 15,111 jobs; all seven new declarations audited;
all 3,066 axiom lists standard-only; all 39 regressions pass. Four new
noncoherent, nonunit endpoint controls exercise the divided prefix and
the actual terminal collision. A separate exact above-binary control
`(0,644,727,217,739,737,443,597)` modulo 1006 has no common touch and all
six proposed two-even-entry pair compressions fail. Thus adding no common
touch does not rescue that unrestricted parity-only shortcut; the critical
range remains essential. It is not a counterexample to G1 or a proof input.
No proof placeholders or `native_decide` were introduced.

### Guardrail for the remaining G1 proof

`G1OverlapCriticality.lean` retains the exact quantitative hypothesis:
for a valid length-`n` tuple, `N + overlap = 2^n + uncovered`, where
`uncovered` counts residues outside the subset-sum cube and its half
translate. Criticality is therefore `uncovered + stratumGap < overlap`.
Overlap greater than the gap alone is insufficient to force common touch,
even at every anchor: the existing valid seven-tuple modulo 1006 has a
three-omission witness, no common touch, and certified all-anchor overlaps
`(16,16,16,40,40,16,24)`, all greater than the first-even gap 2. Its original
anchor leaves 894 residues uncovered. This is not a counterexample to
critical G1 or to deletion; it is a regression against discarding the
ambient-complement term. The three global obligations remain open.

All six declarations are audited. The full 15,076-job build passes, and all
2,737 printed axiom lists use only the standard Lean axioms. The finite
overlap counts use ordinary kernel `decide`, with no proof placeholders or
`native_decide`.

### Proved constraints on the remaining counting argument

`G1CollisionSupportRigidity.lean` proves that a reduced half-collision is
determined by its tail support up to swapping sides. Consequently canonical
collisions have distinct supports, and overlap greater than two forces a
free tail coordinate. In every nontrivial critical tuple, at every anchor,
there is a half-witness light off that anchor and zero at another coordinate.
This excludes the all-full-support case in every dimension and even stratum.
The witness need not be the separately supplied three-omission witness;
a zero coefficient is not an omission.

The same file proves a strict descent rule: adding a second copy of a
coordinate already in a subset can return to the cube only as a smaller
subset that omits that coordinate. These are unconditional constraints,
not a deletion theorem. Returns outside the overlap can still lie in one
cube; reaching enough residues outside both cubes, with multiplicities
controlled, remains unproved. The three global inputs above remain open.
No new conjectural interface or roadmap package is introduced.

Verification: the full 15,077-job build passes. All six new declarations
are audited; all 2,743 printed axiom lists use only the standard Lean
axioms. No proof placeholders or `native_decide` were introduced.

`G1FirstEvenDuplicateEscape.lean` now rules out a closed duplicate-coordinate
family in the first even stratum, `N=2*q` with `q` odd. For a fixed free
coordinate, the collision face is invariant under half translation and
disjoint from its one-step coordinate translate. Oddness makes closure
under the two-step translate impossible. Subset-sum injectivity then turns
that face exit into an actual exit from the overlap. A critical-range
consumer supplies the initial free collision automatically, without G2 or
failure of common touch.

The distinction from uncovered residues is essential: in the existing valid
tuple modulo 1006, one fixed free coordinate has a nonempty collision face
but **all** of its direct duplicate exits lie in exactly one cube. This
regression is kernel-checked. The example is noncritical; it does not refute
G1. The next count must couple different coordinates, use actual criticality
to exclude these one-cube exits, or construct the deleted tuple directly.
No global input is closed and no new conjectural interface is introduced.

Verification: the full 15,078-job build passes; all four new declarations
are audited, and all 2,747 printed axiom lists use only the standard Lean
axioms. The regression uses ordinary kernel `decide`.

### Saturated overlap: actual deletion proved

`G1SaturatedOverlap.lean` closes the case where the whole subset-sum cube
equals its half translate (equivalently, the overlap has cardinality
`2^(n-1)`). A faithful cyclic character factors the cube transform as
`prod (1 + character(diff_i))`. Half-translation invariance makes this
product zero, forcing one difference to be exactly the half modulus.
That antipodal pair gives common touch and an actual valid `(n-1)`-tuple
at half the modulus. Both the set-equality and overlap-cardinality deletion
consumers are proved in all dimensions and even strata, without G2 or G3.

Consequently an unresolved G1 case must have proper overlap at every anchor;
saturated overlap no longer needs a counting argument. This closes a
structural deletion case, not the full three-omission input. Partial overlap,
the general odd threshold, and exceptional lifts remain open. No new
conjectural interface is added.

Verification: full build 15,079 jobs; all five declarations are audited,
and all 2,752 printed axiom lists use only the standard Lean axioms.
No proof placeholders or `native_decide` were introduced.

## Layout

A single Lake package rooted at the repository root:

```
lakefile.toml, lean-toolchain, lake-manifest.json
MinModulus.lean                 -- root module, imports the files below
MinModulus/
  UniqueSums.lean               -- Theorems A, B and the main theorem `nmin_eq`
  ElemAbelian2.lean             -- Proposition 2 (elementary abelian 2-groups)
  AbelianMin.lean               -- Open problem 4 (all finite abelian groups)
  Descent.lean                  -- two-adic halving/deletion lemmas toward Conjecture 1
  G1Triangle.lean               -- three-witness closure and triangle common-touch family
  G1CriticalRange.lean          -- subset-sum overlap and automatic light half-witnesses
  G1OverlapOrbits.lean          -- exact collision model and free half-shift orbit pairing
  G1OverlapSupports.lean        -- explicit collision supports and family-wide attachments
  G1OverlapPadding.lean         -- reduced witness shapes and exact padding multiplicities
  G1ReducedIntersections.lean   -- weighted shapes intersect except for exact opposites
  G1CanonicalIntersections.lean -- canonical intersecting representatives and exact half-weight
  G1CanonicalAttachments.lean  -- internal support-to-omission incidence and weighted mass
  G1AttachmentDeficit.lean     -- positive-tail growth or quantified anchor deficit
  G1LightWitnessReduction.lean -- light attachments fold back into canonical collisions
  G1LightTransitionDescent.lean -- cross-tail, imbalance-drop, or near-balanced dynamics
  G1NearBalancedTransitions.lean -- rigidity and support growth in imbalance zero/one
  G1TransitionIncidenceFibers.lean -- exact residual incidence fibers and coverage inequality
  G1UnitCoreReduction.lean     -- global all-light/non-crossing funnel to imbalance one
  G1HeavyOrCross.lean          -- eliminate residual unit matrix; heavy-or-cross trichotomy
  G1CanonicalCrossing.lean     -- pairwise and weighted density of canonical crossings
  G1CrossingMass.lean          -- total-square split into crossing and diagonal mass
  G1DominantPadding.lean       -- diagonal concentration yields a dominant shape
  G1MinimalSupportTransitions.lean -- escaping transitions cover a minimal support tail
  G1MinimalSupportFibers.lean -- exact avoided-source fiber sum by escape target
  G1DominantStarCrossing.lean -- crossing star forces mass or strict majority
  G1StrictMajorityGrowth.lean -- all escape targets grow support and halve weight
  G1MajoritySupportBound.lean -- critical weight floor forces support codimension
  G1EscapeDepth.lean         -- exact padding loss and aggregate escape-depth tax
  G1RestoredPadding.lean     -- realize lost depth as a full subset-sum value layer
  G1RestoredIntersections.lean -- exact root/restored overlap and three-halves union
  G1RestoredPairwise.lean   -- exact pairwise overlap via blocked-support signatures
  G1BlockedSignatureFibers.lean -- equal signatures have equal escape fibers
  G1SignatureCoverage.lean -- distinct escape signatures retain full tail coverage
  G1SignatureLayers.lean -- intrinsic multiplicity-free restored value layers
  G1LayerSecondMoment.lean -- global union bound for all restored layers at once
  G1SignatureSubcubeCoverage.lean -- sharp union bound from covered coordinates
  G1SignatureUpperFace.lean -- disjoint negative-tail face and full-cube constraint
  G1SignatureIntersectingCoverage.lean -- exact factor two from intersecting coverage
  G1SignaturePositiveFace.lean -- positive-tail upper face or reverse crossing
  G1SignatureCrossingCharge.lean -- charge all avoiding signatures to crossing mass
  G1SignatureHybridBound.lean -- pay upper-face contamination from crossing mass
  G1CriticalHybridSandwich.lean -- small-crossing sandwich and tail-size reduction
  G1GenuineDominantResidual.lean -- retain failed branches; empty tail is near-full
  G1EmptyTailDepthCharge.lean -- exact fiber charge eliminates empty positive tail
  G1DominantFiberWeight.lean -- universal fiber weight and logarithmic support bound
  G1AvoidingFiberCharge.lean -- exact avoiding-fiber crossing charge and incidence split
  G1TailCoveragePartition.lean -- partition B by avoiding versus meeting coverage
  G1SignatureTailSurplus.lean -- sharpen covered signature union to 2w+|B|-2
  G1SignatureTailSlices.lean -- inflate tail surplus by exact padding slices
  G1SignatureThirdSlice.lean -- retain a fixed third-slice surplus with no error
  G1SignatureOrderedSlices.lean -- sum disjoint first-present tail slices
  G1MeetingOrderedSlices.lean -- clean ordered slices from A-meeting signatures
  G1FiberAdaptiveSlices.lean -- retain exact selected escape-fiber slice weights
  G1ThreeDescent.lean           -- delete two coordinates at an order-three difference
  OddOrder.lean                 -- odd-order bound, chain rigidity, linear wedge
  RelationCertificate.lean      -- adjugate/determinant bridge for relation systems
  QuadraticWedge.lean           -- SHC bridge and quadratic/multi-level lemmas
  SubtupleRigidity.lean         -- conditional odd-window subtuple spanning
  SHCBaseCases.lean             -- kernel-checked 3-coordinate SHC bound
  SHCFourBaseCases.lean         -- normalized 4-coordinate window exclusions
  SHCFourGenerator.lean         -- generator coordinates and 4-coordinate SHC bound
  SHCFiveGeneratorReduction.lean -- structural 5-coordinate generator reduction
  SHCFiveGenerator.lean         -- unconditional 5-coordinate window generator theorem
  SHCFiveCertificate.lean       -- trusted bridge for normalized 5-coordinate certificates
  Generated/SHCFiveN*.lean      -- sharded normalized 5-coordinate kernel checks
  SHCFiveBaseCases.lean         -- 5-coordinate SHC bound 63 and odd `n=6` stratum
  SHCSixGeneratorReduction.lean -- structural 6-coordinate generator reduction
  SHCSixGenerator.lean          -- tight 2-prime generator cases
  SHCSixExceptionalCertificate.lean -- trusted order-105 certificate bridge
  Generated/SHCSixN105*.lean   -- sharded order-105 kernel checks
  SHCSixGeneratorComplete.lean  -- full 6-coordinate window generator theorem
  SHCSixCertificate.lean        -- trusted bridge for normalized 6-coordinate certificates
  SHCCardinality.lean           -- uniform cube-plus-translated-layers bounds
  SHCSixCardinality.lean        -- isolated analytic normalized exclusion below 76
  Generated/SHCSixNormalizedN*.lean -- sharded normalized 6-coordinate checks
  SHCSixBaseCases.lean          -- analytic normalized 6-coordinate exclusions through 75
  GlobalRoadmap.lean            -- critical-range G1/G2/G3 interfaces and descent
  G1Counterexample.lean         -- unrestricted G1 refutation outside the critical range
scripts/check_axioms.lean       -- axiom audit, run in CI
scripts/generate-five-normalized-certificates.py -- deterministic Torch certificate generator
scripts/generate-six-exceptional-certificate.py -- deterministic order-105 generator
scripts/generate-six-normalized-certificates.py -- deterministic normalized 6-coordinate generator
```

## Build

| | |
|---|---|
| Toolchain | Lean 4 `v4.32.0`, Mathlib pinned `v4.32.0` (prebuilt cache) |
| Build | `lake build` — green (0 errors, 0 warnings, 0 sorries) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only |

With [elan](https://github.com/leanprover/elan) on your `PATH` (it reads
`lean-toolchain` and fetches Lean `v4.32.0` automatically):

```sh
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build
```

To reproduce the axiom audit:

```sh
lake env lean scripts/check_axioms.lean
```

## What is formalized

The development is stated in **`k`-space over ℕ**: a candidate multiset is
`k : ℕ → ℕ` with `∑_{i<n} k i = n`, validity is the paper's k-vector condition
with `Nat.ModEq`, and the paper's signed multiples $`V = \pm jN`$ appear only
through the congruence `M ≡ 2^n − 1 [MOD N]` on $`M = \sum k_i 2^i`$ — no
integer subtraction anywhere.

| Lean declaration | Corresponds to (paper) | Status |
|---|---|---|
| `a`, `dsum`, `val`, `Supp`, `Valid` | Problem statement, k-vector form | ✅ defined |
| `sum_two_pow`, `sum_a_add_dsum` | §3 reduction identities | ✅ proved |
| `not_valid_of_witness` | Lemma 1 (reduction), witness direction | ✅ proved |
| `val_pad`, `dsum_pad`, `supp_mono`, `update_top`, `shift_*`, `unshift_*` | (plumbing) | ✅ proved |
| `ones_rep`, `ones_erase_rep`, `exists_rep_le`, `exists_rep_lt`, `exists_rep_compl` | §6 Prop. 1 (master achievability criterion), existence half | ✅ proved |
| `dsum_succ_of_lt`, `exists_dsum_eq` | Lemma 3 (digit sum), contiguity (upward) half | ✅ proved |
| **`theoremB`** | **§6 Theorem B — lower bound, all four cases** | ✅ **proved** |
| `gmin`, `gmin_add_le`, `gmin_add_pow`, `gmin_ones` | §4 greedy digit sum $`s_{\min}`$, top-coin / all-ones values | ✅ proved |
| `gmin_le_dsum` | Lemma 3 (digit sum), minimality (downward) half | ✅ proved |
| `ones_unique` | Lemma 2 ($`V \ne 0`$) | ✅ proved |
| `dsum_le_val`, `val_le_dsum_mul` | §3 trivial range $`n \le M \le n \cdot 2^{n-1}`$ | ✅ proved |
| `gmin_step` | §5 Lemma 4 (step), $`s_{\min}(M + 2^n - 2^t) \ge s_{\min}(M) + 1`$ | ✅ proved |
| `slack` | §5 slack bound $`s_{\min}(M_j) \ge n + j`$, induction on $`j`$ | ✅ proved |
| **`theoremA`** | **§5 Theorem A — upper bound / validity** | ✅ **proved** |
| **`nmin_eq`** | **Main theorem, `IsLeast {N ∣ 2 ≤ N ∧ Valid n N} (2^n − 2^m)`** | ✅ **proved** |

## Proposition 2: elementary abelian 2-groups

[`MinModulus/ElemAbelian2.lean`](MinModulus/ElemAbelian2.lean) formalizes
Proposition 2: if $`g_0, \dots, g_{n-1} \in (\mathbb{Z}_2)^k`$ have unique
multiset sums, then $`k \ge n - 1`$. Equivalently, the least elementary abelian
$`2`$-group admitting such a family has order $`2^{n-1}`$.

The theorem `MinModulus.elementaryAbelianTwoGroups_optimal` matches the paper's
statement: `UniqueMultisetSums` quantifies over multiplicity vectors
$`m : \mathrm{Fin}\ n \to \mathbb{N}`$ with $`\sum_i m_i = n`$, and casting
$`m_i`$ into $`\mathbb{Z}_2`$ before scaling gives the correct multiset sum in
$`(\mathbb{Z}_2)^k`$. The conclusion `n - 1 ≤ k` (truncated subtraction) is
equivalent to $`k \ge n - 1`$.

The proof follows the paper's argument: the map $`\Lambda(x) = \sum_i x_i g_i`$
and the coordinate-sum functional are built as linear maps; a nonzero
$`u \in \ker \Lambda \cap \ker(\mathrm{sum})`$ has even positive support $`S`$,
and doubling half of $`S`$ while dropping the other half yields a size-$`n`$
multiset with the same group sum but a multiplicity $`\ne 1`$, contradicting
uniqueness; rank–nullity then gives
$`n = \mathrm{rank}\ \Lambda + \dim \ker \Lambda \le k + 1`$.

The hypothesis is non-vacuous: $`n = 2`$, $`k = 1`$, $`g = (0, 1)`$ satisfies it
and meets the bound with equality.

## Open problem 4: all finite abelian groups

[`MinModulus/AbelianMin.lean`](MinModulus/AbelianMin.lean) formalizes Inal's
resolution of the paper's fourth open problem. Write $`n = m + 1`$. A tuple
`g : Fin (m+1) → G` in a finite abelian group `G` is **valid** (`ValidTuple`) if
the all-ones vector is the only $`k : \mathrm{Fin}\ (m+1) \to \mathbb{N}`$ with
$`\sum_i k_i = m + 1`$ and $`\sum_i k_i \cdot g_i = \sum_i g_i`$. Let
$`m_{\mathrm{ab}}(n)`$ be the least order of a finite abelian group admitting a
valid tuple. Then $`m_{\mathrm{ab}}(n) = 2^{n-1}`$.

The key observation is that validity forces the translated differences
$`g_{j+1} - g_0`$ to be **dissociated**: their subset-sum map
`ssum g : Finset (Fin m) → G` is injective (`ssum_injective`), which embeds the
Boolean cube into `G`.

| Lean declaration | Corresponds to (Inal) | Status |
|---|---|---|
| `ValidTuple`, `diff`, `ssum` | Definitions (validity, differences, subset-sum map) | ✅ defined |
| `not_collision_disjoint`, `ssum_injective` | Lemma 3.1 — validity forces dissociation | ✅ proved |
| **`card_ge`** | **Cor. 3.2 — lower bound `2^(n-1) ≤ |G|`** | ✅ **proved** |
| `elem_valid`, `elem_card` | Prop. 3.3 — sharpness (standard tuple in $`(\mathbb{Z}_2)^{n-1}`$) | ✅ proved |
| **`mab_isLeast`** | **Thm. 1.1 — `m_ab(n) = 2^(n-1)`, as `IsLeast`** | ✅ **proved** |
| `diff_order_two`, `equality_order_two`, `ssum_bijective` | Thm. 4.1 — the extremal group is elementary abelian | ✅ proved |
| **`equality_classification`** | **Thm. 4.1 — differences form an $`\mathbb{F}_2`$-basis** | ✅ **proved** |
| **`equality_addEquiv`** | **Thm. 1.1 — explicit $`\phi : G \to (\mathbb{Z}_2)^{n-1}`$, $`\phi(g_i - g_0) = e_i`$** | ✅ **proved** |

The lower bound `card_ge` holds for *every* finite abelian group, strengthening
Proposition 2 (which is restricted to elementary abelian $`2`$-groups) and the
previously available counting bound $`\binom{2n}{n}/2^n`$. At equality, a second
use of validity (representing $`2(g_i - g_0)`$ as a subset sum and rivalling the
all-ones vector with a multiplicity-3 entry) shows every difference has order
two; combined with the bijectivity of `ssum`, the differences form an
$`\mathbb{F}_2`$-basis, so — up to translation and isomorphism — the only
extremal tuple is $`(0, e_1, \dots, e_{n-1})`$ in $`(\mathbb{Z}_2)^{n-1}`$.

This settles the abelian minimum-order question (open problem 4). It is separate
from Conjecture 1 (minimality of $`N`$ over all residue sets in $`\mathbb{Z}_N`$),
which remains open.

## Progress toward Conjecture 1

The `descent` branch also formalizes the current proof program for global
cyclic optimality.  These results do **not** prove Conjecture 1, but they make
its remaining inputs explicit and kernel-check the reusable parts:

| File / declaration | Result |
|---|---|
| `Descent.lean`: `witness_combination`, `deletion_descent`, `pair_descent` | halving and deletion at the order-two element |
| `common_touched_of_unique_omission` | G1 holds when one half-witness has a unique omitted coordinate |
| `three_witnesses_sum_ne_zero` | excludes the exact minimal cyclic three-witness pattern in G1 |
| `G1Triangle.lean`: `witness_three_sum`, `common_touched_of_three_sum_unique_omission` | the sum of three half-witnesses is another half-witness whenever its coefficients remain at least `-1`; a unique omission in that sum forces a G1 common-touch coordinate |
| `common_touched_of_triangle_one_light_opposite` | closes every exact omission triangle whose opposite coefficients, up to permutation, are `1, ≥2, ≥2`; the summed witness has one omission |
| `witness_compl_sum_eq_card_exactOmissions`, `witness_coeff_eq_zero_or_one_or_two_of_exact_pair` | exact omission set `S` leaves precisely `|S|` positive coefficient mass outside `S`; in particular every non-omitted coefficient of a two-omission witness is `0`, `1`, or `2` |
| `triangle_opposite_coefficients_zero_one_or_two`, `not_triangle_all_opposites_two` | reduces exact triangle opposite profiles to `{0,1,2}³` and excludes `(2,2,2)` because each `2` exhausts its witness's positive mass, forcing the three vectors to sum to zero |
| `triangle_one_one_two_sum_witness_zero_opposite` | reduces the residual positive profile `(1,1,2)` to a new witness on the heavy omission edge with opposite coefficient `0` |
| `exists_pair_difference_witness`, `validTuple_injective`, `common_touched_of_pair_difference` | turns a coordinate difference equal to the half element into an exact one-omission witness and hence a G1 common-touch coordinate; validity in particular makes tuple coordinates distinct |
| `common_touched_of_same_exact_pair_zero_two` | closes a same-edge zero/`2` pair in every group with a unique nonzero involution: validity forces the zero witness to concentrate at another coordinate, equality after doubling yields the involution difference, and the pair bridge closes G1 |
| `zmod_eq_zero_or_half_of_add_self_eq_zero`, `common_touched_of_triangle_one_one_two_zmod` | specializes unique involution to `ZMod (2*M)` and closes the exact cyclic triangle profile `(1,1,2)` outright |
| `triangle_all_one_sum_witness_exact_triple` | reduces the residual profile `(1,1,1)` to a witness whose exact omission set is the three triangle vertices |
| `exists_companion_one_of_exact_pair_coeff_one`, `witness_neg_of_le_one` | exposes the hidden companion coordinate of every light two-omission witness and proves that any witness in the symmetric coefficient window `[-1,1]` remains a half-witness after negation |
| `common_touched_of_triangle_all_one_zmod` | closes the cyclic `(1,1,1)` profile: repeated companion coordinates yield equal doubles and a half-modulus difference, while three distinct companions make the exact-triple witness negatable and contradict validity |
| `common_touched_of_triangle_positive_zmod` | combines the `{0,1,2}` classification with the profile theorems to close every strictly positive exact omission triangle in an even cyclic group |
| `common_touched_of_two_adjacent_light_opposites_zmod` | closes any exact cyclic triangle with two adjacent opposite coefficients equal to `1`, including the zero-containing profile `(0,1,1)` up to rotation |
| `exists_pure_companion_two_of_triangle_zero_opposite`, `two_smul_eq_target_add_pair_of_exact_pair_coeff_two` | proves that a zero-opposite edge must be the pure vector `-p-q+2e`, with `e` outside the triangle and affine doubling relation `2g_e=h+g_p+g_q` |
| `exists_six_distinct_pure_centers_of_triangle_all_zero` | reduces an all-zero exact omission triangle to three pairwise-distinct external pure centers, hence a canonical six-coordinate affine doubling configuration |
| `nonzero_three_torsion_of_two_adjacent_heavy_opposites`, `three_dvd_of_two_adjacent_heavy_opposites_zmod` | shows that two adjacent heavy opposites produce a nonzero coordinate difference killed by `3`; cyclically this forces `3 ∣ N`, so `(0,2,2)` is impossible at every modulus prime to `3` |
| `exists_double_difference_eq_target_of_triangle_zero_two_two`, `four_dvd_of_double_eq_half`, `twelve_dvd_of_triangle_zero_two_two_zmod` | strengthens the exact `(0,2,2)` profile: the pure companion on its zero edge has displacement `x` with `2x=N/2`, forcing `4 ∣ N`; together with adjacent-heavy 3-torsion this forces `12 ∣ N` |
| `witness_neg_pair_sum_at_zero_of_le_one`, `not_two_adjacent_heavy_opposites_of_involution`, `not_two_adjacent_heavy_opposites_at_half_zmod` | closes the branch completely: two adjacent pure heavy witnesses sum to `(1,-2,1)`, whose negative is the forbidden zero-witness `(-1,2,-1)`; consequently `(0,2,2)` is impossible at every even cyclic modulus, superseding its conditional torsion/descent analysis for G1 |
| `witness_two_coeff_sum_le_two_of_exact_pair`, `not_two_adjacent_opposites_of_sum_ge_three`, `triangle_other_opposites_zero_of_opposite_eq_two` | generalizes the sign-flip closure: adjacent opposite coefficients with total at least `3` are impossible, since at most one unit of their positive mass remains off the triangle; hence any opposite `2` forces both neighbors to be `0`, closing `(0,1,2)` and leaving only `(0,0,2)` among profiles containing `2` |
| `double_balanced_center_sum_eq_target_of_pure_triangle`, `four_dvd_of_triangle_{all_zero,zero_zero_two}_zmod` | unifies the remaining pure profiles: the difference between their three coefficient-`2` centers and the three triangle vertices doubles to the half modulus; therefore both `(0,0,0)` and `(0,0,2)` force `4 ∣ N` |
| `common_touched_or_profile_zero_zero_one_of_not_four_dvd_zmod` | packages the exact-triangle frontier at `v₂(N)=1`: every exact omission triangle either supplies the G1 common-touch coordinate or has profile `(0,0,1)` up to rotation |
| `omitted_other_of_zero_at_exact_pair`, `exists_companion_with_neg_exact_pair_of_coeff_one`, `common_touched_or_exists_three_omission_heavy_witness_of_not_four_dvd_zmod` | bridges that last light profile to the non-triangular problem: a witness avoiding the candidate common vertex must omit the two opposite triangle vertices and the light companion, and must have some coefficient at least `2`; thus at `v₂(N)=1` every exact triangle either closes G1 or forces a genuinely higher-mass three-omission witness |
| `witness_coeff_zero_one_two_or_three_of_exact_triple`, `exact_triple_heavy_shape` | classifies the exact-three branch of that escape: its three units of positive mass are either concentrated as a single coefficient `3`, or split uniquely as coefficients `2+1`; otherwise the escape necessarily has a fourth omission |
| `witness_sub_at_zero_of_floor`, `exists_six_distinct_centers_of_triangle_zero_zero_one`, `escape_zero_at_pure_centers_of_triangle_zero_zero_one` | rules out support collisions in the residual profile: its two pure centers and light companion are pairwise distinct, and every exact-three escape has coefficient zero at both pure centers; hence the canonical `3` or `2+1` positive support lies on genuinely new coordinates |
| `three_smul_eq_target_add_triple_of_exact_triple_coeff_three`, `two_smul_add_eq_target_add_triple_of_exact_triple_coeff_two_one`, `add_eq_target_add_pair_of_exact_pair_coeff_one_one`, `exact_triple_heavy_affine_shape_against_light_pair` | evaluates both exact-three shapes and the light edge, then normalizes the escape to a common right-hand side: either `3g_e = g_b + 2g_z`, or `2g_e + g_f = g_b + 2g_z`; this is the clean affine relation system that must be excluded next |
| `exists_shared_omission_of_zero_at_nonzero_coeff`, `exists_touched_in_or_avoidances_share_omission`, `exists_touched_in_or_avoidances_meet_exactOmissions`, `avoidances_meet_exactOmissions_of_no_common_touched` | extracts the global pattern missing from an isolated affine shape: every selected nonzero support coordinate either already closes G1, or has an avoiding witness whose omission set meets the old omission set; under global common-touch failure this sprouts such an attached witness at every selected support coordinate, uniformly for canonical and higher-omission branches |
| `G1CriticalRange.lean`: `two_pow_le_card_add_subsetSumShift_overlap`, `subsetSumShift_overlap_card_gt_of_add_lt` | makes the strict modulus range quantitative: the valid anchored subset-sum cube has `2^m` distinct points, so its overlap with any translate has size at least `2^(m+1)-|G|`; in a critical stratum the half-translate overlap is larger than the exact power of two omitted from the endpoint |
| `subsetCollisionCoeffs`, `witness_of_subsetSum_eq_add`, `exists_light_half_witness_of_lt_two_pow` | converts every half-shifted cube overlap into an explicit half-witness; below `2^(m+1)` one exists automatically and all non-anchor coefficients lie in `{-1,0,1}` |
| `G1OverlapOrbits.lean`: `subsetSumCollisionEquivOverlap`, `subsetSumCollisionSwapEquiv_ne`, `even_card_subsetSumOverlap` | identifies every overlap point uniquely with an ordered collision `(S,T)`; at a nonzero order-two shift, `(S,T) ↔ (T,S)` is fixed-point-free, so the whole overlap decomposes into two-element orbits and has even cardinality |
| `critical_subsetSum_half_overlap_add_two_le` | strengthens the critical overlap count for nontrivial tuples: the even endpoint gap is exceeded by at least two points, not merely one; the remaining task is to exploit the supports of these paired collisions to force common touch or a disjoint layer |
| `G1OverlapSupports.lean`: `mem_subsetCollisionSupport_iff`, `subsetCollisionCoeffs_exactOmissions`, `orientSubsetSumCollision_omissions_nonempty` | describes every oriented collision witness by explicit finite sets: its tail support is `S∆T`, its omissions are `T\S`, and a nonzero half target guarantees that negative tail is nonempty |
| `commonTouched_or_all_subsetSumCollision_supports_sprout_avoidances` | applies the no-common-touch expansion simultaneously to the full overlap family: either G1 already holds, or every explicit support coordinate of every oriented collision sprouts an avoiding half-witness omitting a coordinate in that collision's negative tail |
| `G1OverlapPadding.lean`: `subsetSumCollisionEquivReducedPadding`, `card_collisionPadding` | uniquely decomposes every collision into a disjoint reduced relation `(A,B)` and common padding outside `A∪B`; each reduced witness shape has exact multiplicity `2^(m-|A∪B|)` |
| `card_subsetSumOverlap_eq_sum_reduced_weights` | rewrites the full translated-cube overlap exactly as the sum of those padding weights over all reduced collision shapes, exposing rather than hiding the multiplicity that the next no-common-touch count must control |
| `critical_reduced_collision_weight_lower_bound` | restates the strict critical modulus inequality on genuine witness shapes: their exact padding weights sum to at least the endpoint gap plus two |
| `G1ReducedIntersections.lean`: `reducedCollision_negative_tails_inter_or_eq_swap` | applies witness combination to the weighted shapes: two cardinality-oriented reduced negative tails intersect unless the shapes are the exact fixed-point-free swaps of one another |
| `reducedCollision_negative_tails_inter_of_card_lt`, `reducedCollision_swapped_weight` | removes the exception whenever one oriented shape is strictly unbalanced and proves that every remaining balanced opposite pair carries equal padding weight |
| `G1CanonicalIntersections.lean`: `canonicalReducedCollision_negative_tails_inter`, `sum_reducedCollisionWeight_eq_two_mul_canonical` | selects exactly one member of every reduced swap pair (using cardinality and a balanced tie-breaker), proves the selected negative tails are pairwise intersecting, and identifies their exact weight as one half of the full overlap weight |
| `critical_canonicalReducedCollision_weight_half_lower_bound`, `criticalCanonicalReducedCollisions_negative_tails_inter` | specializes the canonical family to the strict two-adic range: it is pairwise intersecting and carries weight at least `2^(min(s+1, log₂(n+1))-1)+1`; the next G1 step is to combine this large weighted family with the support-avoidance attachments |
| `G1CanonicalAttachments.lean`: `reducedSubsetSumCollision_eq_of_right_eq`, `canonicalReducedNegativeTails_pairwise_inter` | validity makes the negative-tail projection injective, so the canonical collisions give an honest pairwise-intersecting finite set family with no hidden multiplicity |
| `commonTouched_or_canonicalReducedCollisions_internal_attachments`, `commonTouched_or_canonicalReducedCollisions_right_card_two_le` | under common-touch failure, every vertex of every canonical tail has an attached half-witness which vanishes there and omits a different vertex of the same tail; in particular every tail has size at least two |
| `commonTouched_or_critical_internalAttachmentPairs_weight_lower_bound` | packages the new quantitative frontier: either critical G1 already closes, or ordered internal support-to-omission incidences carry weighted mass at least the endpoint gap plus two; the remaining task is to bound witness multiplicity across these incidences or turn them into a disjoint layer |
| `G1AttachmentDeficit.lean`: `attachedWitness_omits_left_or_anchor_deficit` | subtracts an attached witness from its canonical collision witness and invokes validity: either the attachment creates an omission on the positive tail or its anchor coefficient falls below the collision anchor by more than one |
| `balanced_attachedWitness_omits_left`, `commonTouched_or_balancedCanonicalReducedCollisions_cross_attachments` | eliminates the anchor-deficit branch for balanced shapes; every negative-tail vertex then sprouts a witness omitting coordinates on both the positive and negative tails, giving the next cross-tail incidence layer |
| `G1LightWitnessReduction.lean`: `subsetCollisionCoeffs_witnessTails`, `exists_canonicalReducedCollision_coeff_eq_or_neg_of_tail_light` | proves the converse to the overlap construction: every half-witness whose tail coefficients are at most one is, up to sign, exactly another canonical reduced collision; the anchor coefficient is recovered from the zero-sum identity |
| `commonTouched_or_canonicalReducedCollisions_heavy_or_light_transition` | sharpens every canonical attachment: either it has a genuinely heavy tail coefficient `≥2`, or it transitions to another canonical shape which avoids the zero coordinate `j`, with the shared omitted coordinate lying on the sign-determined side |
| `G1LightTransitionDescent.lean`: `positive_lightTransition_cross_or_imbalance_drop`, `negative_lightTransition_imbalance_le_one` | supplies a monotone invariant for the light dynamics: a positive-sign transition either creates an old-positive/new-negative crossing or lowers `|B|-|A|` by at least two, while a negative-sign transition lands at imbalance at most one |
| `reducedCollisionImbalanceDrop_wellFounded`, `reducedCollisionImbalanceDrop_chain_bound`, `commonTouched_or_canonicalReducedCollisions_structured_light_transition` | proves that the non-crossing strict-drop branch has no cycles and that a chain of length `k` consumes at least `2k` initial imbalance; globally, every attachment is now heavy, cross-tail, strictly descending, or near-balanced |
| `G1NearBalancedTransitions.lean`: `positive_nearBalanced_lightTransition_cross`, `negative_nearBalanced_lightTransition_cross_or_unit_imbalances` | resolves the anchor arithmetic at imbalance zero/one: positive-sign transitions must cross the source positive tail, and a non-crossing negative-sign transition can only go from imbalance one to imbalance one |
| `three_le_source_negative_tail_card_of_negative_lightTransition`, `five_le_reducedCollision_support_card_of_unit_imbalance`, `commonTouched_or_balancedCanonicalReducedCollisions_heavy_or_cross` | uses pairwise negative-tail intersection to split the source tail across the target; the residual unit-to-unit branch has at least three negative-tail vertices and five support coordinates, while balanced sources have only heavy or cross-tail attachments |
| `G1TransitionIncidenceFibers.lean`: `mem_negativeTransitionIncidencePairs_iff`, `card_negativeTransitionIncidencePairs` | identifies the exact incidence fiber from source `r` to a negative-sign target `q` as `(B_r \ (A_q∪B_q)) × (B_r∩A_q)`, including the exact product cardinality |
| `unitNegativeTransitionAvoidedCoordinates_eq_right`, `right_card_le_sum_unitNegativeTransition_fibers` | in the all-light, non-crossing unit-source branch, proves that the sigma of exact target fibers covers every source negative-tail coordinate and derives the explicit sum-of-products realization-multiplicity inequality |
| `G1UnitCoreReduction.lean`: `no_balanced_canonicalReducedCollision_of_allLight_noCross`, `exists_canonical_imbalanceDecrease_of_ne_unit` | globalizes the branch split: if all half-witnesses are light and no distinct canonical target crosses its source positive tail, balanced canonical collisions are impossible and every non-unit collision has a strictly smaller-imbalance canonical successor; actual targets are distinct because they avoid a source-tail coordinate |
| `exists_unit_canonicalReducedCollision_reachable`, `right_card_le_sum_unitNegativeTransition_fibers_of_allLight_noCross` | applies well-founded induction to funnel every canonical collision into the unit-imbalance core and packages the exact residual row inequality for every unit source in that global branch |
| `G1HeavyOrCross.lean`: `unitNegativeTransitionIncidences_eq_empty_of_noCross`, `exists_distinct_canonical_positiveTail_cross_of_allLight` | eliminates the residual unit matrix: its diagonal fiber has no avoided coordinate, while every distinct target fiber has empty omission factor by reverse no-cross, contradicting unit-tail coverage |
| `commonTouched_or_heavy_halfWitness_or_distinctCanonicalCross`, `critical_commonTouched_or_heavy_halfWitness_or_distinctCanonicalCross` | reduces every nonempty canonical family, and in particular every critical-range instance, to common touch or one of two explicit quantitative escape branches: a heavy half-witness or a positive-tail crossing between distinct canonical shapes |
| `G1CanonicalCrossing.lean`: `reducedCollision_reverse_cross_or_imbalance_gap`, `distinct_canonicalReducedCollisions_positive_negative_cross` | subtracts any two distinct canonical collision witnesses: absence of a reverse crossing forces their imbalances apart by at least two, and applying this in both directions proves that every unordered distinct pair crosses in one orientation |
| `card_canonicalDistinctPairs_le_two_mul_crossPairs`, `sum_canonicalDistinctPairWeights_le_two_mul_crossPairWeights`, `critical_canonicalCrossPairs_dense` | turns pairwise crossing into density: oriented crossings contain at least half of all ordered distinct pairs, both by cardinality and by the product of their exact padding weights; the remaining crossing count is therefore a diagonal-weight concentration problem, alongside the genuinely heavy branch |
| `G1CrossingMass.lean`: `sum_canonicalDistinctPairWeights_add_diagonal_eq_square`, `square_sum_canonicalWeights_le_two_crossMass_add_diagonal` | identifies ordered-distinct product weight exactly as the square of total canonical weight minus the diagonal squared weights, then bounds that off-diagonal mass by twice the oriented crossing mass |
| `critical_square_gap_le_two_crossMass_add_diagonal`, `critical_crossingMass_or_diagonalConcentration` | inserts the certified critical half-gap weight: either four times the crossing mass controls its square, or twice the diagonal squared-weight sum does; the next step is to bound crossing realization multiplicity and show that diagonal concentration forces a directly chargeable dominant shape or heavy witness |
| `G1DominantPadding.lean`: `two_mul_sum_canonicalWeights_le_card`, `reducedCollision_support_card_le_of_weight_le`, `exists_canonical_weight_mul_sum_ge_diagonal` | bounds total canonical padding weight by half the group order, identifies maximum padding weight with minimum reduced-support size, and bounds diagonal squared-weight mass by maximum weight times total weight |
| `critical_diagonalConcentration_exists_dominantCollision`, `critical_crossingMass_or_exists_dominantCollision` | eliminates the abstract diagonal sum from the critical interface: either crossing mass controls the squared half-gap, or one explicit maximum-weight shape satisfies the stronger relative bound `L² ≤ 2·w_r·TotalWeight` (and, secondarily, `L² ≤ N·2^(n-|A∪B|)`); the next structural step must compare this dominant shape with the transitions forced by common-touch failure |
| `G1MinimalSupportTransitions.lean`: `commonTouched_or_heavy_or_minSupportCanonicalEscapes`, `commonTouched_or_heavy_or_minSupportEscapeIncidences_cover` | applies every forced attachment to a support-minimal shape: unless common touch or a heavy witness occurs, each negative-tail coordinate has a distinct-target canonical transition that avoids it and introduces support outside the source; the finite escape-incidence projection covers the whole negative tail |
| `G1MinimalSupportFibers.lean`: `card_canonicalSupportEscapeIncidences_eq_sum_avoided`, `commonTouched_or_heavy_or_minSupportEscapeFiber_sum` | reorganizes escape incidences by target: an externally escaping target `q` has exact fiber `B_r\(A_q∪B_q)`, giving the concrete multiplicity inequality `|B_r| ≤ ∑_q |B_r\(A_q∪B_q)|` over external targets |
| `card_sourceTail_sdiff_le_card_externalSupport_of_support_card_le`, `commonTouched_or_heavy_or_minSupport_externalSupport_sum` | uses support minimality to charge every avoided source-tail coordinate to a newly introduced target-support coordinate, yielding `|B_r| ≤ ∑_q |(A_q∪B_q)\(A_r∪B_r)|` |
| `G1DominantStarCrossing.lean`: `weight_mul_sum_erase_le_canonicalCrossMass`, `square_le_four_crossMass_or_total_lt_two_weight` | orients every pair incident to a fixed collision toward an actual crossing and injects the weight-preserving star into crossing pairs; a diagonal-controlling shape therefore either forces the fourfold crossing bound or has strict majority of total canonical padding weight |
| `G1StrictMajorityGrowth.lean`: `canonical_other_support_growth_of_strictMajority`, `canonicalSupportEscapeTarget_growth_of_strictMajority` | strict majority makes the dominant shape the unique support minimum: every other canonical target has strictly larger support and at most half its padding weight; every actual escape target also introduces strictly more external coordinates than the source-tail fiber it absorbs |
| `G1MajoritySupportBound.lean`: `support_card_add_le_of_weightFloor_and_strictMajority`, `critical_strictMajority_support_bounds` | combines the certified critical total-weight floor with strict majority: for `a=min(s+1,log₂(n+1))`, the dominant shape satisfies `|A_r∪B_r|+a≤n+1`, equivalently its padding complement has at least `a-1` coordinates |
| `G1EscapeDepth.lean`: `canonical_other_exact_depth_of_strictMajority`, `card_add_sum_supportDepth_le_sum_externalSupport_of_strictMajority`, `sum_other_pow_depth_mul_weight_eq_card_mul_dominantWeight` | makes the target loss exact: depth `d=|supp(q)|-|supp(r)|` gives `w_r=2^d w_q` and `|external|=|dropped|+d`; after escape coverage, `|B_r|+Σd≤Σ|external|`, while restoring each target's `d` binary dimensions produces exactly one full `w_r`-sized padding layer |
| `G1RestoredPadding.lean`: `card_restoredCollisionPadding`, `restoredCollisionValue_injective`, `card_restoredCollisionValueLayer` | realizes the formal `2^d` multiplier: select `d` external target coordinates, pair their powerset with every legal target padding, and map the product injectively to ordinary subsets and—under validity—to group values; every non-root strict-majority target now carries a concrete `w_r`-element sublayer of the anchored subset-sum cube |
| `G1RestoredIntersections.lean`: `card_restoredValueLayer_inter_rootPaddingValueLayer`, `canonicalSupportEscapeTarget_two_mul_restored_inter_root_le`, `three_mul_weight_le_two_mul_card_root_union_restored_of_escape` | computes the root/restored intersection exactly as restoration choices times padding outside both supports; an actual escape target drops at least one root coordinate, so the intersection is at most `w_r/2` and its union with the root padding layer has at least `3w_r/2` distinct subset-sum values |
| `G1RestoredPairwise.lean`: `restoredCollisionSubsetLayer_eq_powerset_allowed`, `card_restoredValueLayers_inter`, `blockedSupport_eq_or_two_mul_restored_inter_le` | identifies each restored layer with the coordinate subcube avoiding its blocked-support signature; all blocked signatures have root-support cardinality, pairwise intersections have an exact powerset formula, and distinct signatures overlap in at most `w_r/2`, giving a `3w_r/2` union; equal-signature target clusters are the remaining multiplicity obstruction |
| `G1BlockedSignatureFibers.lean`: `rootSupport_sdiff_blockedSupport_eq_droppedSupport`, `canonicalSupportEscapeTargetFiber_eq_sourceTail_sdiff_blockedSupport`, `canonical_other_escapeTargetFiber_eq_of_blockedSupport_eq_of_strictMajority` | proves that a blocked signature agrees with its target support on root coordinates, so its root complement is exactly the dropped support and its source-tail complement is exactly the escape fiber; equal-signature strict-majority targets therefore contribute identical coverage and can be collapsed before the global layer count |
| `G1SignatureCoverage.lean`: `canonicalSupportEscapeBlockedSignatures`, `card_escapeBlockedSignature_eq_rootSupport`, `canonicalSupportEscapeBlockedSignatureCoverage_eq_sourceTail` | quotients actual escape targets by their blocked signatures; every realized signature has root-support cardinality and a nonempty source-tail fiber, and the union of these distinct fibers is exactly `B_r`, so target multiplicity is removed without weakening full escape coverage |
| `G1SignatureLayers.lean`: `blockedSignatureValueLayer`, `card_escapeBlockedSignatureValueLayer_eq_rootWeight`, `two_mul_card_escapeBlockedSignatureValueLayers_inter_le`, `two_mul_card_escapeBlockedSignatureValueLayer_inter_root_le` | defines the restored layer intrinsically as the subset-sum image of `P(univ\C)`, avoiding any representative choice; every realized signature layer has size `w_r`, distinct signature layers overlap in at most `w_r/2`, and each overlaps the root padding layer in at most `w_r/2` |
| `G1LayerSecondMoment.lean`: `square_sum_card_le_union_card_mul_sum_pair_inter`, `two_mul_card_mul_weight_le_succ_mul_familyUnion_card`, `two_mul_signatureCount_succ_mul_weight_le` | double-counts point multiplicities to identify the first moment with total layer mass and the second with ordered intersection mass; Cauchy plus the diagonal/off-diagonal split proves `2kw≤(k+1)|⋃L_i|`; applied to the root plus `t` distinct signature layers, `2(t+1)w_r≤(t+2)|Root∪⋃_C Layer_C|` |
| `G1SignatureSubcubeCoverage.lean`: `finset_sdiff_cover_single_or_incomparable`, `pow_card_mul_two_mul_root_le_covered_signature_union_add_root`, `pow_sourceTailCard_mul_two_mul_weight_le_signatureValueUnion_add_weight` | uses the exact coordinate cover rather than only pairwise intersections: either one signature drops all of `B_r`, or two dropped fibers are incomparable and expose disjoint private-coordinate half-cubes; in both cases the root-plus-signature value union is at least `(2-2^{-|B_r|})w_r`, in subtraction-free form `2^{|B_r|}·2w_r≤2^{|B_r|}|Union|+w_r` |
| `G1SignatureUpperFace.lean`: `sourceTail_inter_escapeBlockedSignature_nonempty`, `pow_sourceTailCard_mul_two_weight_add_tailFace_le_unionWithUpper_add_weight`, `pow_sourceTailCard_mul_two_weight_add_tailFace_le_fullCube_add_weight` | canonical negative-tail intersection and root-protected restoration make every realized signature meet `B_r`; hence the face of all subsets containing `B_r`, of size `2^{m-|B_r|}`, is disjoint from the whole covered lower union.  After scaling, this face contributes exactly `2^m`, giving `2^{|B_r|}·2w_r+2^m≤2^{|B_r|}|EnrichedUnion|+w_r` and the corresponding full-cube numerical constraint |
| `G1SignatureIntersectingCoverage.lean`: `finset_sdiff_cover_incomparable_of_inter_nonempty`, `two_mul_weight_le_escapeBlockedSignatureValueUnion`, `two_mul_weight_add_tailFace_le_escapeValueUnionWithUpper`, `two_mul_weight_add_tailFace_le_fullCube` | combines the two decisive facts on the same signature family: its complements cover `B_r`, but every signature intersects `B_r`.  The single-full-drop branch is therefore impossible, two incomparable fibers exist, and the lower value union has the exact factor-two bound `2w_r≤|Union|`; adjoining the disjoint tail-upper face gives `2w_r+2^{m-|B_r|}≤|EnrichedUnion|≤2^m` |
| `G1SignaturePositiveFace.lean`: `all_escapeSignatures_meet_positiveTail_or_exists_reverseCross`, `two_weight_add_tailUpperFaces_le_fullCube_add_weight`, `exists_escapeTarget_reverseCross_or_twoTailUpperFaces_fullCube` | splits on incidence with `A_r`: if every signature meets it, the `A_r`- and `B_r`-upper faces are both disjoint from the lower union and overlap exactly in the full-root upper face, forcing `2w_r+2^{m-|A_r|}+2^{m-|B_r|}≤2^m+w_r`; otherwise an actual escape target avoids `A_r`, so canonical pairwise crossing forces the reverse oriented crossing `(q,r)` into `B_r` |
| `G1SignatureCrossingCharge.lean`: `image_positiveTailAvoidingEscapeTargets_eq_signatures`, `positiveTailAvoidingReverseCrossPairs_subset_crossPairs`, `avoidingSignatureCard_mul_weight_le_crossMass` | retains all signatures avoiding `A_r`: they are exactly the blocked-signature image of actual avoiding targets, and those targets inject into distinct reverse pairs `(q,r)` in the canonical crossing relation.  Since every target padding weight is positive, `(# avoiding signatures)·w_r≤CrossMass`, quantitatively linking signature incidence failure to the existing global crossing budget |
| `G1SignatureHybridBound.lean`: `card_upperSubsetLayer_inter_blockedSubsetLayer`, `pow_positiveCard_mul_contamination_le_crossMass`, `pow_positiveCard_mul_rootWeight_add_tailUpperCards_le_fullCube_add_crossMass` | computes every `A_r`-upper/signature-lower intersection exactly, bounds their union after `2^{|A_r|}` scaling by the avoiding-signature charge, and pays it from canonical crossing mass.  For nonempty `A_r` this gives `2^{|A_r|}(w_r+2^{m-|A_r|}+2^{m-|B_r|})≤2^{|A_r|}2^m+CrossMass`, a single all-dimensions inequality coupling the dominant Boolean faces to the global crossing budget |
| `G1CriticalHybridSandwich.lean`: `criticalHalfGap_square_le_two_pow_succ`, `criticalSmallCrossDominant_hybrid_sandwich`, `criticalSmallCrossDominant_not_both_tail_cards_one`, `critical_crossingMass_or_commonTouched_or_heavy_or_smallCrossDominantEscape` | retains `4·CrossMass<L²` in the dominant branch and sandwiches it against the hybrid face bound.  Since `L²≤2^{n+1}`, the profile `|A_r|=|B_r|=1` would force `2^{n+1}≤4·CrossMass<L²`, a contradiction.  Thus the strengthened all-dimensions critical residual has `A_r=∅` or at least one tail of size at least two |
| `G1GenuineDominantResidual.lean`: `critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant`, `two_le_card_canonicalSupportEscapeBlockedSignatures`, `eight_mul_weight_lt_halfGapSquare_of_genuine_left_empty`, `right_card_add_two_mul_criticalIndex_ge_of_genuine_left_empty` | retains no-common-touch and no-heavy together with strict small crossing.  If `A_r=∅`, all signatures are avoiding while intersecting coverage supplies at least two, so `8w_r<L²`; unique omission also gives `|B_r|≥2`.  Comparing powers yields `n+4≤|B_r|+2min(s+1,log₂(n+1))`, forcing the negative tail to occupy all but `O(log n)` coordinates |
| `G1EmptyTailDepthCharge.lean`: `two_mul_escapeFiberCard_le_targetWeight_of_left_empty`, `two_mul_sourceTailCard_mul_weight_le_crossMass_of_left_empty`, `genuine_left_empty_depth_charge_and_majority`, `genuineDominant_positiveTail_nonempty` | uses `|E_q|=|D_q|+d` and `w_r=2^d w_q` to upgrade each empty-tail escape fiber to `2|D_q|≤w_q`; summing gives `2|B_r|w_r≤CrossMass`, while strict majority gives `2|B_r|<w_r`.  Together with strict small crossing and logarithmic power bounds these inequalities contradict each other, eliminating `A_r=∅` uniformly |
| `G1DominantFiberWeight.lean`: `two_mul_escapeFiberCard_le_targetWeight`, `two_mul_sourceTailCard_le_sum_escapeTargetWeights`, `two_mul_negativeTailCard_lt_weight_of_genuineDominant`, `supportCard_add_log_negativeTail_add_two_le_of_genuineDominant`, `critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_fiberWeight` | removes the empty-positive-tail hypothesis from the depth-weighted fiber estimate: every source-tail fiber lies in the full dropped support, so exact support exchange still gives `2|fiber_q|≤w_q`.  Coverage and strict majority imply `2|B_r|<w_r` for every genuine dominant residual, equivalently `|supp(r)|+log₂|B_r|+2≤n`; the critical-range package retains this all-dimensions padding constraint together with `A_r≠∅` |
| `G1AvoidingFiberCharge.lean`: `two_mul_sum_avoidingFiberCard_mul_rootWeight_le_crossMass`, `two_mul_rootWeight_le_crossMass_of_avoidingEscapeTarget`, `eight_mul_weight_lt_halfGapSquare_of_genuine_of_avoidingTarget`, `log_negativeTail_add_five_lt_two_mul_criticalIndex_of_genuine_of_avoidingTarget`, `rootWeight_add_tailUpperFaces_le_fullCube_or_log_negativeTail_small`, `critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_avoidingFiberDichotomy` | reinserts exact target weights into the reverse-crossing map: avoiding fibers cost `2w_r` per covered incidence, so one avoiding target forces `8w_r<L²`.  Combining its padding upper bound with the universal fiber lower bound yields `log₂|B_r|+5<2min(s+1,log₂(n+1))`; otherwise every signature meets `A_r` and the clean two-upper-face bound `w_r+2^{n-|A_r|}+2^{n-|B_r|}≤2^n` holds |
| `G1TailCoveragePartition.lean`: `positiveTailAvoidingCoveredSourceTail`, `two_mul_avoidingCoveredCard_mul_rootWeight_le_crossMass`, `sourceTail_sdiff_avoidingCovered_subset_meetingCoverage`, `genuineDominant_tailCoverage_partition`, `critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_tailCoveragePartition` | partitions the entire dominant negative tail at coordinate level.  If `X_r` is covered by avoiding targets, then `2|X_r|w_r≤CrossMass`; its exact complement is covered by blocked signatures meeting `A_r`.  In the genuine critical residual, `2|B_r|<w_r` upgrades this to `16|X_r||B_r|<L²`, forcing a large tail predominantly into the meeting-signature regime needed for the next protected-subcube count |
| `G1SignatureTailSurplus.lean`: `two_mul_root_add_tailCard_le_covered_signature_union_add_two`, `two_mul_root_add_tailCard_add_tailFace_le_fullCube_add_two`, `two_mul_weight_add_negativeTailCard_add_tailFace_le_fullCube_add_two`, `pow_positiveCard_mul_rootWeight_add_negativeTailCard_add_tailUpperCards_le_fullCube_add_crossMass_add_error`, `criticalSmallCrossDominant_tailSurplus_hybrid_sandwich` | sharpens intersecting signature coverage from `2w_r` to `2w_r+|B_r|-2`: after choosing the two incomparable private-coordinate half-cubes used by the old proof, every other covered tail coordinate contributes a singleton outside that counted family.  The surplus survives the disjoint `B_r`-upper face and, after scaling by `2^{|A_r|}`, the hybrid estimate retains the full `2^{|A_r|}(|B_r|-2)` gain while contamination is still charged to crossing mass |
| `G1SignatureTailSlices.lean`: `blockedSignatureSingletonTailSlice`, `card_blockedSignatureSingletonTailSlice`, `card_mul_pow_padding_sub_tailCard_le_coveredSlices`, `two_mul_root_add_tailCard_mul_sliceWeight_le_covered_union_add_two_sliceWeights`, `two_mul_weight_add_weightedNegativeTail_add_tailFace_le_fullCube_add_error`, `pow_positiveCard_mul_rootWeight_add_weightedNegativeTail_add_tailUpperCards_le_fullCube_add_crossMass_add_error`, `criticalSmallCrossDominant_tailSlice_hybrid_sandwich` | inflates each leftover singleton to the full realizing-layer slice with exact tail intersection `{j}`.  Such a slice has size `2^{n-|C∪B_r|}≥2^{n-|supp(r)|-|B_r|}`, and slices indexed by distinct coordinates are disjoint.  Hence the surplus beyond `2w_r` becomes `(|B_r|-2)2^{n-|supp(r)|-|B_r|}`; the disjoint upper face, contaminated positive face, crossing charge, and strict critical sandwich all retain this padding-weighted gain |
| `G1SignatureThirdSlice.lean`: `two_mul_root_add_thirdSlice_le_covered_signature_union`, `two_mul_root_add_thirdSlice_add_tailFace_le_fullCube`, `two_mul_weight_add_thirdSlice_add_negativeTailFace_le_fullCube`, `rootWeight_add_thirdSlice_add_tailUpperCards_le_fullCube_add_contamination`, `pow_positiveCard_mul_rootWeight_add_thirdSlice_add_tailUpperCards_le_fullCube_add_crossMass`, `eight_mul_thirdSlice_eq_weight_of_genuineDominant`, `criticalSmallCrossDominant_thirdSlice_hybrid_sandwich` | when `3≤|B_r|`, chooses one covered coordinate beyond the two private half-cube coordinates and frees every coordinate outside the resulting three-coordinate pattern.  This gives the error-free lower union `2w_r+2^{n-|supp(r)|-3}`.  The universal fiber bound forces at least three padding coordinates in the genuine residual, so the added term is exactly `w_r/8`.  It remains disjoint from the opposite tail face, survives cancellation against positive-face contamination, and reaches the strict critical sandwich with no right-hand correction |
| `G1SignatureOrderedSlices.lean`: `orderedGeometricTailSurplus`, `coveredOrderedTailSliceAt_disjoint`, `orderedGeometricTailSurplus_le_card_coveredOrderedSlices`, `two_mul_root_add_orderedGeometricTailSurplus_le_covered_signature_union`, `rootWeight_add_orderedGeometricTailSurplus_add_tailUpperCards_le_fullCube_add_contamination`, `pow_positiveCard_mul_rootWeight_add_orderedGeometricTailSurplus_add_tailUpperCards_le_fullCube_add_crossMass`, `criticalSmallCrossDominant_orderedGeometricTailSurplus_hybrid_sandwich` | orders the `|B_r|-2` coordinates beyond the private markers and assigns each the subsets for which it is the first present ordered marker.  Slice `i` fixes only `i+3` markers, later tail coordinates remain free, and distinct first-present patterns are disjoint.  The resulting error-free surplus is the canonical geometric sum `Σ_{i<|B_r|-2}2^{n-|supp(r)|-(i+3)}`.  The full sum survives the opposite face, contamination cancellation, crossing charge, and strict critical sandwich; for `|B_r|=2` it specializes uniformly to zero |
| `G1MeetingOrderedSlices.lean`: `orderedMeetingTailSurplus`, `coveredMeetingOrderedTailSliceAt_disjoint`, `orderedMeetingTailSurplus_le_card_coveredMeetingOrderedSlices`, `orderedMeetingTailSurplus_add_twoUpperFaces_le_fullCube`, `orderedMeetingTailSurplus_add_tailUpperFaces_le_fullCube`, `genuineDominant_avoidingCharge_and_meetingGeometricFaces` | returns to the exact avoiding/meeting partition of `B_r`.  A signature meeting `A_r` and (as every escape signature does) `B_r` yields slices automatically disjoint from both upper faces, so slice `i` fixes only `i+1` ordered meeting markers and needs no contamination charge.  If `X` is avoiding-covered and `Y=B_r\X`, the genuine residual simultaneously satisfies `16|X||B_r|<L²` and `Σ_{i<|Y|}2^{padding-(i+1)}+2^{n-|A_r|}+2^{n-|B_r|}≤2^n`.  This is a stronger all-dimensional invariant, though symbolic profiles remain and require a multi-root count |
| `G1FiberAdaptiveSlices.lean`: `selectedCoveringSignature`, `card_selectedFiberTailSlices`, `root_add_selectedFiberSliceMass_le_rootAndSignatureUnion`, `selectedFiberSliceMass_eq_sum_pow_padding_sub_fiberCard`, `root_add_selectedFiberSliceMass_add_tailFace_le_fullCube`, `weight_add_selectedFiberSliceMass_add_negativeTailFace_le_fullCube`, `max_twoWeight_rootAddSelectedFiberMass_add_negativeTailFace_le_fullCube`, `genuineDominant_max_factorTwo_fiberAdaptive_tailFace_bound` | selects one realizing signature `C_j` per covered coordinate and keeps the exact singleton-tail slice size `2^{padding-|B_r\C_j|}` instead of replacing every fiber by `|B_r|`.  Different coordinates give disjoint slices, so their exact mass `M_r` adds to the root and opposite tail face.  The critical residual retains `max(2w_r,w_r+M_r)+2^{n-|B_r|}≤2^n`; singleton-fiber stars contribute `w_r/2` per coordinate and can therefore break the old factor-two ceiling |
| `G1MinimumFiberBudget.lean`: `selectedCoveringSignature_fiberCard_le`, `realizingEscapeTargetForSignature_injOn`, `sum_realizingEscapeTargetWeights_lt_rootWeight`, `two_mul_escapeBlockedSignatureFiberCardSum_lt_rootWeight`, `selectedFiberSliceMass_eq_sum_selectedSignatureMultiplicities`, `selectedFiberSliceMass_eq_sum_multiplicity_mul_pow_padding_sub_fiberCard`, `sum_selectedCoveringSignatureMultiplicities`, `selectedCoveringSignatureMultiplicity_le_fiberCard`, `selectedCoveringSignatureCoverage_eq`, `two_mul_selectedCoveringSignatureFiberSum_lt_rootWeight`, `genuineDominant_minimumFiber_groupedBudget_and_tailFace_bound`, `two_singleton_minimumFiber_profile_remains_feasible` | upgrades the coordinate selector to a minimum-cardinality covering fiber and chooses one actual target per distinct signature.  Signature representatives inject into the non-root canonical targets, so strict majority gives `Σ_C w_{q_C}<w_r`; the pointwise fiber tax then yields `2Σ_C|B_r\C|<w_r`.  If `t_C` coordinates select `C`, then `Σ_Ct_C=|B_r|`, `t_C≤|B_r\C|`, and the exact slice mass regroups as `M_r=Σ_Ct_C2^{padding-|B_r\C|}`.  The selected signatures still cover `B_r` and retain the adaptive cube inequality.  A checked two-singleton profile shows these one-root constraints remain feasible for `(|A_r|,|B_r|,padding)=(1,2,d)`, `d≥3`, forcing the next count to couple the selected target roots |
| `G1TwoSingletonCoupling.lean`: `two_singleton_escapeTargets_common_negative_outside`, `two_singleton_omissionFan_exact_triangle_or_tail_growth`, `exists_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two`, `genuineDominant_two_selectedEscapeTargets_common_negative_outside_of_tail_card_two` | couples the two roots forced by the surviving `|B_r|=2` profile.  Writing `B_r={j,k}`, the minimum signatures have fibers `{j}` and `{k}` and yield distinct actual targets `q,u`.  Pairwise intersection of canonical negative tails forces the omission fan `k∈B_q`, `j∈B_u`, and a common `z∈B_q∩B_u` with `z∉B_r`.  Either the new tails are exactly `{k,z}` and `{j,z}`, forming the three-edge triangle, or one has cardinality at least three.  This is a genuine multi-root constraint and the structural split for the next expansion/count |
| `G1TwoSingletonTriangle.lean`: `canonicalReducedCollision_exactOmissions_of_negativeTail_eq_pair`, `canonical_exactTriangle_two_zero_allZero_or_commonTouched_or_heavyThree_zmod`, `heavy_coordinate_eq_anchor_of_not_criticalHeavy`, `one_le_criticalIndex_of_four_dvd`, `genuineDominant_two_tail_zeroOppositeTriangle_or_growth` | bridges a pair-valued canonical negative tail to the exact successor omission set of its light collision witness.  In the exact fan, singleton fibers already make the two target-opposite coefficients zero.  If the root opposite is also zero, the all-zero triangle retains an explicit `t` with `t+t=N/2`, forces `4∣N`, and hence has critical index `s≥1`.  Otherwise it equals one, so the light-triangle theorem gives common touch or a three-omission witness with a coefficient at least two.  Since the genuine residual excludes both common touch and heavy successor coefficients, any such heavy coefficient is exactly the anchor.  Its `|B_r|=2` branch is therefore: an explicit half-of-half center at positive 2-adic depth, anchor-heavy three-omission expansion, or target-tail growth |
| `G1QuarterCenterTransport.lean`: `balancedSixCoeffs`, `quarterCenter_cast_eq_half`, `criticalQuarterCenter_cast_eq_previousHalf`, `exists_light_balancedSix_halfWitness_after_cast_of_triangle_all_zero`, `canonical_exactTriangle_two_zero_light_halfWitness_after_cast_zmod` | upgrades the all-zero obstruction from divisibility to a transported witness.  If `N=2M=4K` and `t+t=M`, reduction `ZMod N → ZMod M` sends `t` to the nonzero involution `K`; in the critical form this is exactly the preceding layer's half target `2^(s-1)q`.  The all-zero exact triangle supplies `t` as the balanced value of three pairwise-distinct pure centers minus three pairwise-distinct triangle vertices.  `balancedSixCoeffs` turns these signs into an actual `Witness` for the coordinatewise-reduced tuple and proves every coefficient is at most one.  The canonical singleton fan exposes the six coordinates and this light half-witness explicitly.  The reduced tuple is not claimed valid—original half-witnesses reduce to zero relations—so the next use must couple this new relation back to the original collision family rather than recursively invoke G1 unchanged |
| `G1QuarterWitnessQuartet.lean`: `balancedPairCoeffs`, `pureEdgeCoeffs`, `balancedSix_add_quarterPairs_eq_pureEdges`, `exists_light_quarterWitness_quartet_of_triangle_all_zero`, `canonical_exactTriangle_two_zero_quarterWitness_quartet_zmod` | keeps the quarter structure upstairs.  An all-zero triangle produces four light witnesses at one target `t` with `2t=N/2`: the balanced six-point witness omits the original vertex triple, while three balanced-pair witnesses omit the three edges of the pure-center triangle.  Their coefficient identities are exact: adding the six-point witness to each opposite pair witness recovers the corresponding original pure half-witness.  The canonical exact-fan wrapper exposes the quartet, its exact omission hypergraph, the pure-center incidences, and all three decomposition identities, providing a four-layer object for a padding-weighted count |
| `G1QuarterLayerCount.lean`: `reducedCollisionOfTailLightWitness`, `four_distinct_reducedCollisionWeights_le_overlap`, `exists_four_distinct_quarterLayers_of_triangle_all_zero`, `canonical_exactTriangle_two_zero_four_quarterLayers_zmod` | converts every tail-light witness at an arbitrary target into its disjoint positive/negative reduced collision and reconstructs the full coefficient vector, so distinct vectors have disjoint exact padding fibers.  The quarter quartet therefore contributes four separate weights to `R∩(R+t)`.  Its six-point shape has tail support at most six and each pair shape at most four, yielding the dimension-uniform lower bound `2^(m-6)+3·2^(m-4)≤|R∩(R+t)|`, as well as the sharper exact sum of the four actual padding weights.  The result is packaged directly for the canonical all-zero singleton fan |
| `G1TwoSingletonAllZero.lean`: `subsetCollisionCoeffs_heavy_coordinate_eq_anchor`, `canonical_exactTriangle_two_zero_not_allZero_zmod`, `genuineDominant_two_tail_anchorHeavy_or_growth` | eliminates the all-zero branch from the canonical singleton fan.  Every successor coefficient of a subset-collision vector is at most one, so each coefficient-`2` pure center forced by an all-zero triangle must be the anchor.  The triangle theorem makes its three centers pairwise distinct, giving an immediate contradiction.  Hence the genuine `|B_r|=2` residual has only two live exits: an arbitrary half-witness with three distinct omissions and coefficient at least two at the anchor, or a selected escape target whose negative tail has cardinality at least three.  The quarter-transport/counting theorems remain valid for generic all-zero witness triangles, but their canonical specializations have inconsistent hypotheses and are not a live G1 branch |
| `G1AnchorHeavyGrowth.lean`: `exists_canonicalReducedCollision_of_anchorHeavy_three_omissions`, `genuineDominant_two_tail_exists_canonical_tail_growth` | reconstructs the surviving anchor-heavy, successor-light witness as a canonical reduced collision.  Its anchor coefficient is exactly the negative/positive tail-cardinality imbalance, so anchor mass at least two gives imbalance at least two; the three distinct non-anchor omissions all lie in its negative tail, giving cardinality at least three.  Combined with the explicit escape-target exit, every genuine dominant root with `|B_r|=2` therefore produces a distinct canonical collision with negative tail at least three, carrying either strict imbalance or escape-target provenance |
| `G1AnchorHeavyExchange.lean`: `isRootSeparatedRestoredLayer_of_support_card_le_of_dropped_nonempty`, `genuineDominant_two_tail_escape_growth_or_anchor_exchange`, `genuineDominant_two_tail_exists_rootSeparated_tail_growth` | retains the geometry discarded by the coordinate-free three-omission output.  In the anchor-heavy branch the reconstructed collision contains all of `B_r` and drops a coordinate of `A_r`; otherwise an actual selected escape target already has negative tail at least three.  Consequently every genuine dominant two-tail root produces a strictly support-growing, factor-two-lighter collision with negative tail at least three and a full restored layer of root weight whose intersection with the root padding layer is at most half that weight |
| `G1AnchorExchangeSignature.lean`: `restoredCollisionBlockedSupport_ne_of_root_mem_avoid_mem`, `genuineDominant_two_tail_escape_growth_or_three_blocked_signatures` | converts the retained support exchange into signature multiplicity.  The two selected targets omit opposite coordinates of `B_r`, whereas the anchor-exchange collision contains both.  Their blocked signatures are therefore pairwise distinct.  Unless a selected target already has negative tail at least three, the genuine two-tail branch contains three distinct full root-weight restored layers, each quantitatively separated from the root padding layer |
| `G1AnchorExchangePrivateSlices.lean`: `exists_canonical_anchorExchange_of_light_triangle`, `five_mul_root_le_two_mul_root_three_private_signature_union`, `genuineDominant_two_tail_escape_growth_or_privateSlice_tailFace_charge` | keeps the exchange collision coupled to the same exact fan.  The two selected signatures and the exchange signature each uniquely allow one of three root-support coordinates, producing three pairwise-disjoint half-cubes disjoint from the root cube.  Hence the lower union has at least `5w_r/2` values; the opposite two-tail upper face is also disjoint, giving `5w_r+2·2^(n-2)≤2|U|` for an explicit `U` inside the anchored subset-sum cube, unless selected target-tail growth has already occurred |
| `G1AnchorExchangePositiveFace.lean`: `anchorExchange_privateSlice_hybrid_surplus`, `genuineDominant_two_two_tail_escape_growth_or_privateSlice_sandwich` | inserts the private exchange into the positive-face hybrid count.  With `P=2^|A_r|`, its surviving surplus is exactly `(P-2)w_r`: the singleton-positive branch is a genuine one-root barrier, while `|A_r|≥2` retains a positive padding-weighted gain after crossing contamination |
| `G1SupportGrowthAmortization.lean`: `supportDepth_two_or_tiny_of_smallCross`, `genuineDominant_two_tail_rootWeight_ge_three`, `genuineDominant_two_tail_exists_quarterWeight_growth`, `three_mul_sum_tail_le_head_of_four_mul_chain` | turns strict small crossing into a multi-root decay mechanism.  Exact depth and the crossing star force every non-root target to have depth at least two except for the unique boundary `(L,w_r,w_v,d)=(3,2,1,1)`.  The two distinct selected targets force `w_r≥3`, eliminating that boundary when `|B_r|=2`.  Thus the geometry-preserving larger-tail target grows support by at least two and has `4w_v≤w_r`; along any iterated factor-four chain, three times the total later weight is bounded by the initial weight |
| `G1SupportStarConcentration.lean`: `genuineDominant_two_tail_four_mul_crossStarWeight_le_rootWeight`, `genuineDominant_two_tail_four_mul_totalCanonicalWeight_le_five_mul_rootWeight`, `genuineDominant_two_tail_all_other_eighthWeight_growth`, `genuineDominant_two_tail_four_mul_nonrootCard_le_rootWeight` | applies strict small crossing to the whole non-root star.  Its total padding weight is at most `w_r/4`, so the root carries at least four fifths of all canonical weight and the number of non-root targets is at most `w_r/4`.  Because the coupled fan supplies a second positive-weight target beside any chosen target, equality at depth two would overfill the quarter budget; consequently every non-root canonical collision grows support by at least three and satisfies `8w_v≤w_r`.  This globally budgets every terminal target rather than following one chosen path |
| `G1RestorationFanPacking.lean`: `restorationFan_normalized_packing`, `genuineDominant_two_tail_exists_dropped_eighthWeight_growth`, `genuineDominant_two_tail_exists_restorationFan_tailFace_packing` | pays the depth-normalization multiplier geometrically.  A depth-`d` target dropping a root coordinate has `d+1` alternative restoration supports obtained from one external `(d+1)`-set; their blocked signatures are pairwise distinct and root-sized.  Including the root gives `d+2` full `w_r` layers with pairwise intersection at most `w_r/2`, all inside the anchored cube.  Both live two-tail exits retain the required dropped coordinate and have `d≥3`, so the fan occupies at least `5w_r/3`; canonical negative-tail intersection adjoins the disjoint `B_r`-upper face and yields `2(d+2)w_r+(d+3)2^(n-2)≤(d+3)|U|`, hence `5w_r+3·2^(n-2)≤3|U|≤3·2^n` |
| `G1RestorationFanExactUnion.lean`: `restorationFanSubsetUnion_eq_lower_sdiff_upper`, `card_restorationFanValueUnion`, `genuineDominant_two_tail_exists_restorationFan_exact_tailFace_packing` | replaces the fan's second-moment estimate by its exact coordinate geometry.  If `H` is the chosen external `(d+1)`-set, the fan signatures are `(supp(v)\H)∪{e}`.  Their union is the enlarged lower cube avoiding `supp(v)\H`, minus the face containing all of `H`; the excluded face is in bijection with target paddings.  Hence the fan has exactly `2w_r-w_v≥15w_r/8` values.  Its union with the disjoint `B_r`-upper face has exact size `(2w_r-w_v)+2^(n-2)` and satisfies `15w_r+8·2^(n-2)≤8|U|≤8·2^n` in the live two-tail residual |
| `G1PairedRestorationFans.lean`: `pow_card_mul_card_upper_inter_restorationFanSubsetUnion`, `two_mul_card_pairedRestorationFanValueUnion`, `genuineDominant_two_tail_exists_pairedRestorationFan_packing` | couples the two selected targets forced by a two-coordinate root tail.  Restrict the fan of the target dropping `j` to subsets containing `j`, and symmetrically for `k`.  The two directional slices have root-tail patterns `(1,0)` and `(0,1)`, while the root layer has `(0,0)` and the full negative upper face has `(1,1)`, so all four pieces are disjoint.  Exact fan factorization gives `2|L|=6w_r-w_v-w_u`; all-target factor-eight decay yields `23w_r≤8|L|`.  The live global packing is `23w_r+8·2^(n-2)≤8|U|≤8·2^n` |
| `G1PairedRestorationPositiveFace.lean`: `positiveTail_inter_targetNegativeTail_of_drops_one_contains_other`, `two_mul_card_pairedRestorationFanValueUnionWithTailUpperFaces`, `genuineDominant_two_tail_exists_pairedRestorationFan_twoFace_packing` | computes the positive-face behavior of the paired fans.  A canonical target dropping `j` and containing `k∈B_r` cannot cross back through `B_r`, so canonical pairwise crossing forces `A_r∩B_v≠∅`; the positive upper face is therefore disjoint from both complete fans.  The two root upper faces overlap only in the full-root upper face of size `w_r`, giving the exact doubled count `2|U|=4w_r-w_v-w_u+2·2^(n-|A_r|)+2·2^(n-2)`.  For `|A_r|=1`, this is an exact near-tiling: `2|U|+w_v+w_u=2^(n+1)` and the anchored-cube complement has doubled cardinality `w_v+w_u` |
| `G1PairedRestorationComplement.lean`: `restorationFanCommonBlockedSupport_eq_rootSupport_erase`, `subsetSumRange_sdiff_pairedRestorationFanValueUnionWithTailUpperFaces` | identifies the near-tiling deficit exactly.  A target dropping `j` has fan common block `supp(r)\{j}`; its directional root cell splits into the forced fan slice and one excluded face of doubled size `w_q`.  For the two selected targets, the anchored-cube value complement is exactly the union of those two concrete excluded value faces |
| `G1PairedRestorationTransport.lean`: `ssum_restorationFanExcludedTransport_of_singletonPositive`, `restorationFanForcedExcludedTranslatedValueSlice_eq_transport`, `two_mul_card_pairedRestorationFanExcludedTransportValueUnion` | transports every excluded face through its target collision.  Writing `E_q=B_q∩H_q`, the fixed shift is `h+ssum(E_q)` and the translated face is exactly `Upper(B_q∪{j})∩Lower(A_q)` inside the full-root upper face.  Canonical pairwise crossing makes the two selected transports disjoint, so their union has doubled size `w_v+w_u`; this proves the one-root geometry is saturated and redirects the roadmap to shift-labelled transport across multiple roots |
| `G1TransportCycles.lean`: `FinsetAffineTransport.comp`, `translateValuePath_exists_escape_or_card_nsmul_sum_eq_zero`, `restorationFanTransportCycle_addOrderOf_shift_dvd_pow` | retains the affine labels under arbitrary finite composition.  A translation path either contains a value outside its starting face, or its total shift is annihilated by that face's cardinality.  Each live excluded restoration face has exact size `2^(m-|supp(q)|-1)`, so a closed composite based there has 2-primary total shift.  This corrects the naive claim that a directed cycle automatically gives a forbidden zero-target relation: the remaining G1 step must first construct compatible multi-root paths and then exclude their 2-primary cycle shifts (or charge every escape as genuinely new mass) |
| `G1TransportOddProjection.lean`: `zmod_castHom_eq_zero_of_pow_two_nsmul_eq_zero`, `zmod_castHom_eq_zero_iff_mem_zmultiples`, `restorationFanTransportPath_oddProjection_sum_eq_zero`, `zmod_castHom_restorationFanCollisionShift_half` | extracts the cyclic arithmetic content of the 2-primary constraint.  Any power-of-two-annihilated element of `ZMod N` vanishes modulo every odd divisor of `N`; hence a closed shift path based at a restoration face has zero total label in the odd quotient, equivalently an integer multiple of the odd part in the original group.  At `N=2^(s+1)q`, the half target vanishes modulo `q`, so the projected edge label `h+ssum(B_c∩H_c)` is exactly the projected restoration-support sum.  The remaining graph theorem can now aim at a concrete odd-quotient zero relation |
| `G1TransportFaceMatching.lean`: `restorationFanTransportFace_eq_nextExcluded_iff`, `targetPositive_card_eq_two_of_restorationFace_match`, `two_mul_card_restorationFanTransportValueFace_inter_nextExcluded_le`, `restorationFanTransportFace_disjoint_oppositeExcludedSource` | audits the missing edge condition before iterating transport.  Source and transported target slices are Boolean faces; exact equality is equivalent to equality of their forced and forbidden coordinate sets, and can occur only when the current target has exactly two positive coordinates.  At equal support rank every non-two-positive successor source captures at most half the transported value face, while the opposite source at the same root is disjoint.  Thus any compatible path must genuinely re-root, and the remaining global step is an aggregate coverage/escape estimate (with the two-positive exact profile handled separately), not merely finite graph iteration. |
| `G1TransportFaceCoverage.lean`: `pow_mul_card_booleanConstraintFaces_inter_le_of_constraintGrowth`, `pow_le_card_of_booleanConstraintFace_subset_biUnion_of_constraintGrowth`, `pow_supportGrowth_mul_card_restorationFanTransportValueFace_inter_nextExcluded_le`, `reducedCollisionWeight_le_sum_of_transportValueFace_cover` | makes the successor obstruction quantitative and aggregate.  A face fixing `d` more coordinates captures at most a `2^-d` fraction of the transported face, so any such cover needs at least `2^d` sources.  More generally, if live re-rooted excluded value faces cover a transported target, the sum of their collision padding weights is at least the current target weight.  This is the dimension-independent interface needed to compare genuine successor coverage directly with the existing canonical-star weight budget. |
| `G1TransportBalancedCover.lean`: `balanced_biUnion_cover_rigidity`, `balanced_biUnion_cover_incidence_margins`, `liveRestorationEdgeDatum_exists_globalEscape_or_balancedRigidity` | globalizes coverage over a finite family.  `LiveRestorationEdgeDatum` packages each genuine edge; its source and transported target both have half the target collision's padding weight, and distinct canonical targets make all transported faces pairwise disjoint.  Therefore either their union contains a value outside every source face, or total mass balance is rigid: source and target unions coincide, the source faces are also pairwise disjoint, and all target-source intersections form an exact integer incidence matrix with prescribed row and column sums.  The remaining equality branch is now a finite face-partition classification problem rather than an uncontrolled iterative graph. |
| `G1TransportPiecewisePermutation.lean`: `PartitionedAffineTransport.map_injective`, `PartitionedAffineTransport.orbitShiftSum_orderOf_toPerm_eq_zero`, `liveRestorationEdgeDatum_exists_globalEscape_or_positiveOrbit_zero_shift` | converts the rigid equality branch into genuine dynamics.  Affine edges between two partitions of one finite value set assemble into an injective—and hence bijective—piecewise translation.  Iteration is translation by the recursively accumulated selected edge shifts; at the positive order of the resulting permutation every point returns, so that literal accumulated shift is zero.  For live restoration data each selected label is exactly `-(h+ssum(B_q∩H_q))`.  Thus a nonempty canonical family now has the global dichotomy required by the roadmap: a value escaping every source face, or an actual compatible point-orbit with zero total restoration shift. |
| `G1TransportSubsetOrbit.lean`: `LiveRestorationPermutationSystem.sourceSubsetAt_toPerm`, `orbitSourceSubset_succ`, `mem_orbitSourceSubset_succ_iff`, `orbitSourceSubset_orderOf_eq` | lifts a rigid point orbit uniquely back to ordinary subsets using validity.  If edge `q_t` is selected at step `t`, the exact coordinate recurrence is `S_(t+1)=B_(q_t)∪(S_t\supp(q_t))`: the target support is overwritten by its negative tail and every outside padding coordinate is retained.  At the positive permutation order the subset itself returns exactly.  The cycle branch is therefore reduced to a finite coordinate-overwrite classification, making explicit when zero total shift is mere telescoping and where a nontrivial witness or monotone support obstruction must arise. |
| `G1TransportLastWrite.lean`: `mem_orbitSourceSubset_add_iff_of_untouched`, `mem_orbitSourceSubset_after_last_touch_iff`, `exists_last_touch_initial_iff_negative` | classifies each coordinate in a closed overwrite orbit.  An untouched interval preserves its membership bit; if step `k` is the last target support containing a coordinate, the terminal bit is exactly whether that coordinate lies in `B_(q_k)`.  Since the subset orbit closes, every touched coordinate's initial bit equals this last negative-tail bit (and a last positive-tail write forces initial absence).  This turns recurrence into explicit last-occurrence constraints ready to combine with canonical crossing and support-depth growth. |
| `G1TransportSameRootObstruction.lean`: `restorationFanTransportFace_disjoint_ownExcludedSource`, `pairedRestorationFanTransportValue_disjoint_sameRootSources` | closes the local-successor audit.  A transported target forces the whole live root support, whereas its own excluded source avoids the other root-negative coordinate; it is therefore disjoint from its own source as well as the opposite source handled previously.  For the two selected targets, the complete transported value union is disjoint from the complete same-root source union.  Hence the already-constructed local pair cannot seed the balanced permutation: any genuine successor family must contain new roots, and failure to re-root still requires a separate novelty argument relative to the full near-tiling. |
| `G1TransportLiveProfileObstruction.lean`: `genuineDominant_liveRoot_all_other_support_card_six_le`, `genuineDominant_liveRoot_unique_one_two_profile`, `not_liveRestorationPermutationSystem_of_all_roots_canonical` | completes the profile audit and rules out the proposed recurrent live graph inside the actual canonical family.  The live dominant root has support size three; every other canonical collision in the genuine residual has support size at least six, so the dominant root is the unique canonical one-positive/two-negative collision.  Every canonical-root live edge therefore has that same root, but arbitrary same-root transported targets are disjoint from arbitrary same-root sources.  Hence no nonempty rigid restoration permutation system can have all roots canonical.  The global proof must now charge the non-live large-support profiles directly; the conditional cycle machinery cannot be the main G1 closure. |
| `G1LargeSupportUpperFacePacking.lean`: `pow_negativeCard_mul_reducedCollisionWeight_eq_positiveUpper_card`, `sixteen_mul_positiveCardStratumWeight_le_succ_mul_upperUnion`, `genuineDominant_liveRoot_largeSupport_positiveUpper_packing`, `genuineDominant_liveRoot_largeSupport_positiveUpper_with_quarterBudget` | starts the corrected direct global packing.  Canonical orientation and support at least six force every non-root negative tail to have at least three coordinates, so its positive upper face has at least eight times its native padding weight.  The complete non-root family is partitioned exactly by positive-tail cardinality; within each stratum validity makes the positive tails distinct, equal-size upper faces overlap by at most one half, and the second-moment count gives `16 W_a ≤ (k_a+1)|U_a|`.  The critical theorem supplies these inequalities simultaneously with the existing quarter-star budget.  The remaining load-bearing step is now precise: control duplication between different cardinality strata and contamination of their combined upper union with the paired restoration packing. |
| `G1PositiveUpperNesting.lean`: `two_mul_card_blockedSignatureUpperValueLayers_inter_le_of_not_subset`, `two_mul_positiveUpperIncidenceMass_sq_le_union_mul_pairBudget`, `genuineDominant_liveRoot_largeSupport_positiveUpper_allFamily` | combines all positive-cardinality strata into one upper-face union.  A larger forced positive tail gives a contained upper face; conversely, if `A_q` is not contained in `A_u`, their intersection has at most half of the `A_u`-face.  Thus complete cross-stratum duplication occurs only through strict positive-tail nesting.  An explicit ordered `PairBudget` pays the diagonal and exactly these comparable pairs, and the all-family second moment plus the factor-eight supply yields `128 W^2 ≤ |U| PairBudget`, with `|U|≤2^n`.  The next theorem must charge strict positive-tail containments using the genuine residual's no-heavy-witness/canonical-crossing constraints, then bound contamination of `U` with the paired restoration packing. |
| `G1PositiveUpperNestingCharge.lean`: `strictPositiveNesting_forces_reverse_canonicalCross`, `positiveUpperPairBudget_eq_card_succ_mul_incidence_add_two_mul_nesting`, `positiveUpperNestingFaceMass_le_canonicalCrossFaceMass`, `genuineDominant_liveRoot_largeSupport_positiveUpper_nestingCharged` | charges the complete strict-nesting loss to canonical crossing geometry.  If `A_q⊂A_u`, disjointness rules out `A_q∩B_u`, so pairwise canonical crossing forces `A_u∩B_q`; swapping strict nesting pairs is therefore an injection into the oriented crossing relation.  The pair budget decomposes exactly as `(|F|+1)S+2N`, where `S` is upper-face incidence mass and `N` is strict-nesting face mass, and `N` is at most the new face-weighted oriented crossing mass.  The remaining quantitative bridge is to compare this face-weighted mass with the already small product-weight crossing mass, or absorb it together with the paired restoration union. |
| `G1PositiveUpperCrossingNormalization.lean`: `canonicalCrossFaceMass_eq_productPaid_add_supportCrowded`, `productPaidCrossFaceMass_le_canonicalProductCrossMass`, `supportCrowdedPair_ambient_lt_support_add_negativeCard`, `supportCrowdingSurplus_le_negative_inter_support_card`, `genuineDominant_crossFaceMass_small_up_to_supportCrowded` | performs the exact normalization split left by the nesting charge.  On a crossing `(r,q)`, `|Upper(A_r)|=2^|B_r|w_r`; if `2^|B_r|≤w_q`, the face is paid term-by-term by `w_rw_q`.  The complementary pair satisfies `n<|supp(q)|+|B_r|`, and its full exponent surplus is bounded by `|B_r∩supp(q)|`.  Thus the whole face-weighted crossing mass is at most the old product crossing mass plus one explicit support-crowded face mass; in the genuine residual, four times it is below the critical gap square plus four times that crowded residual.  The next global step is to turn the certified overlap surplus into restoration-packing capacity. |
| `G1PositiveUpperNestedCrowding.lean`: `positiveUpperNestingFaceMass_eq_productPaid_add_supportCrowded`, `productPaidPositiveUpperNestingFaceMass_le_canonicalProductCrossMass`, `strictPositiveNesting_reducedCollisionImbalance_drop`, `crowdedStrictPositiveNesting_surplus_le_negative_inter_negative_card`, `genuineDominant_liveRoot_largeSupport_positiveUpper_nestedCrowding` | sharpens the normalization to the actual nesting pairs instead of enlarging the error to every crossing.  The product-paid nested faces inject into canonical product crossing mass; only crowded strict nesting remains.  For `A_q⊂A_u`, its full crowding surplus is realized in `B_u∩B_q`, and validity forces `imbalance(u)+2≤imbalance(q)`, so nesting chains have length at most half their initial imbalance.  The all-family quadratic packing now contains only product crossing mass plus crowded-nesting face mass.  The next theorem should turn the shared-negative-tail surplus and decreasing imbalance into disjoint restoration slices. |
| `G1PositiveUpperAdjacentNesting.lean`: `four_mul_positiveUpper_inter_le_two_faces_add_diagonal_adjacent`, `two_mul_sum_positiveUpper_pairInter_le_card_mul_incidence_add_diagonal_add_adjacent`, `oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentNestingBudget`, `genuineDominant_liveRoot_largeSupport_positiveUpper_adjacentNesting` | corrects the ordered-pair overcharge by pairing both orientations.  If `A_q⊂A_u` has cardinality gap `d`, the two baselines contribute `(2^d+1)|Upper(A_u)|` against four copies of the intersection.  Thus gaps `d≥2` need no extra term, while `d=1` needs exactly one—not two—copy of the smaller face.  The sharp family budget is `|F|S+S+N_adj`, and the factor-eight second moment yields `128W²≤|U|(|F|S+S+N_adj)`.  Only adjacent positive-tail nesting remains to normalize and pack. |
| `G1PositiveUpperAdjacentCrowding.lean`: `adjacentPositiveNestingFaceMass_le_productCrossMass_add_crowdedAdjacent`, `adjacentPositiveNesting_negativeCard_growth`, `adjacentPositiveNesting_supportCard_mono`, `adjacentPositiveNesting_uniqueFlip`, `oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentCrowdingBudget`, `genuineDominant_liveRoot_largeSupport_positiveUpper_adjacentCrowding` | product-normalizes the exact adjacent residual: `N_adj≤X_prod+N_adj,crowded`, so `128W²≤|U|(|F|S+S+X_prod+N_adj,crowded)`.  Every unpaid adjacent edge `A_q⊂A_u` has `|B_u|+1≤|B_q|`, `|supp(u)|≤|supp(q)|`, shared negative-tail surplus, and `A_u\A_q` is a singleton contained in `B_q`.  This identifies the residual as a directed coordinate flip with nonincreasing support, ready for the dropped-support/contained-support split. |
| `G1PositiveUpperAdjacentSupportSplit.lean`: `supportCrowdedAdjacentFaceMass_eq_fanLive_add_contained`, `fanLiveCrowdedAdjacent_restorationFan_packing`, `containedAdjacentPositiveNesting_negative_sSubset`, `containedAdjacentPositiveNesting_negativeDiff_eq_flip_union_external`, `oneHundredTwentyEight_mul_sum_weight_sq_le_positiveUpperUnion_mul_adjacentSupportSplitBudget`, `genuineDominant_liveRoot_largeSupport_positiveUpper_adjacentSupportSplit` | partitions `N_adj,crowded=N_fan+N_contained` according to whether `supp(u)\supp(q)` is nonempty.  Since `|supp(u)|≤|supp(q)|`, every live edge supplies the existing normalized restoration fan with root `u`, target `q`, wholly inside the subset-sum range.  Otherwise `supp(u)⊆supp(q)` and `B_u⊂B_q`, with the exact disjoint decomposition `B_q\B_u=(A_u\A_q)∪(supp(q)\supp(u))`; the flip term has size one.  The next step is a family-level bounded-multiplicity packing of the live fans and a direct charge for this rigid contained branch. |
| `G1PositiveUpperContainedFlipFan.lean`: `commonTouched_of_equalSupport_adjacentPositiveNesting`, `containedAdjacentFlipFan_normalized_packing`, `genuineResidual_containedCrowdedAdjacent_supportCard_lt`, `genuineResidual_containedCrowdedAdjacent_flipFan` | turns the rigid contained branch into a second fan mechanism.  Equal support makes twice the unique anchored flip difference zero; uniqueness of the nonzero involution then gives common touch, so the genuine residual has strict support growth.  At depth `d`, exchanging the flip coordinate with each of the `d` external coordinates, together with the root signature, gives `d+1` distinct root-cardinality layers with pairwise half-overlap.  Hence `2(d+1)w_u≤(d+2)|U_flip(u,q)|`, with `U_flip(u,q)⊆subsetSumRange(g)`.  Both support branches now have local normalized fans; the remaining issue is family-level reuse and contamination. |
| `G1PositiveUpperAdjacentFanWithUpper.lean`: `reducedCollisionPositiveUpperValueUnionAll_eq_subsetSumRange_of_left_empty`, `fanLiveCrowdedAdjacent_restorationFan_packing_with_positiveUpper`, `containedCrowdedAdjacent_flipFan_packing_with_positiveUpper`, `adjacentCrowded_fullRange_or_fans_with_positiveUpper` | corrects the scale of the local fan interface.  The residual charge attached to an adjacent edge is the complete face `Upper(A_u)`, not merely `w_u`.  If `A_q` is empty then its upper face already equals the whole subset-sum range.  Otherwise the live restoration fan and the contained flip fan are respectively disjoint from `Upper(A_u)`, so their normalized root-weight gains can be adjoined to that entire face without loss.  This supplies a correct full-face local packing for every crowded adjacent edge.  The remaining load-bearing step is a family-level ownership or bounded-multiplicity theorem for these enlarged unions; summing the per-edge inequalities directly is not yet justified. |
| `G1PositiveUpperAdjacentMultiplicity.lean`: `card_crowdedAdjacentIncomingPairs_le_positiveCard`, `card_crowdedAdjacentOutgoingPairs_le_negativeCard`, `supportCrowdedAdjacentFaceMass_eq_sum_incomingMultiplicity`, `two_mul_supportCrowdedAdjacentFaceMass_eq_sum_outgoingMultiplicity`, `genuineDominant_liveRoot_largeSupport_positiveUpper_adjacentMultiplicity` | supplies the first family-level ownership theorem.  Validity identifies a collision from its positive tail, so crowded adjacent edges form a simple directed Boolean-lattice graph.  Incoming edges at `u` delete distinct coordinates of `A_u`, while outgoing edges at `q` flip distinct coordinates of `B_q`; hence `indeg(u)≤|A_u|` and `outdeg(q)≤|B_q|`.  Regrouping the exact edge-face mass gives `N_crowded=Σ_u indeg(u)|Upper(A_u)|` and, using the adjacent factor-two face ratio, `2N_crowded=Σ_q outdeg(q)|Upper(A_q)|`.  Thus the residual is bounded simultaneously by positive- and negative-cardinality vertex moments.  The next numerical step is to absorb one of these moments using the full-face fan unions/shared-negative surplus, rather than treating edge unions independently. |
| `G1PositiveUpperParityPacking.lean`: `adjacentPositiveNestingPairs_evenPositiveCard_eq_empty`, `adjacentPositiveNestingPairs_oddPositiveCard_eq_empty`, `oneHundredTwentyEight_mul_evenPositiveCardWeight_sq_le`, `oneHundredTwentyEight_mul_oddPositiveCardWeight_sq_le`, `thirtyTwo_mul_sum_weight_sq_le_even_or_odd_positiveUpper_packing`, `genuineDominant_liveRoot_largeSupport_positiveUpper_parityPacking` | removes the adjacent residual by a rank-coloring argument.  An adjacent strict nesting changes `|A|` by one, so neither the even nor odd positive-cardinality subfamily contains such an edge; nesting gaps at least two were already free in the symmetric face estimate.  Each parity class therefore satisfies the residual-free coefficient-128 packing `128W_p²≤|U_p|(|F_p|S_p+S_p)`.  Since one parity carries at least half the total padding weight, the whole family has a residual-free coefficient-32 packing in one of the two classes, with `|U_p|≤2^n`.  This supersedes adjacent fan aggregation for controlling duplication internal to the positive-upper union.  The remaining global issue is contamination of the selected parity union with the dominant-root paired near-tiling, together with a numerical bound on its incidence term. |
| `G1PositiveUpperParityIncidence.lean`: `two_mul_positiveUpperIncidenceMass_le_card_succ_mul_union_of_adjacent_zero`, `sixteen_mul_evenPositiveCardWeight_le_card_succ_mul_union`, `sixteen_mul_oddPositiveCardWeight_le_card_succ_mul_union`, `sixteen_mul_sum_weight_le_card_add_two_mul_positiveUpperUnion`, `genuineDominant_liveRoot_largeSupport_positiveUpper_parityIncidence` | cancels the common incidence factor in each residual-free parity second moment, obtaining `16W_p≤(|F_p|+1)|U_p|`.  Summing both parity inequalities avoids choosing a heavy class: the weights and vertex counts partition exactly, while both `U_p` lie in the full union.  Hence the complete family satisfies the clean all-rank bound `16W≤(|F|+2)|U|`, `|U|≤2^n`, with only the constant two-color overhead and no nesting/crossing/crowding term.  Internal positive-upper duplication is now closed.  The remaining G1 packing task is to control how this full union intersects the dominant-root paired near-tiling and to exploit the cardinality factor using the quarter-star/profile constraints. |
| `G1PositiveUpperPairedComplement.lean`: `restorationFanForcedExcludedValueSlice_subset_positiveUpperValueLayer`, `pairedRestoration_complement_subset_positiveUpperValueUnionAll`, `positiveUpperValueUnionAll_sdiff_pairedRestoration_eq_complement`, `genuineDominant_two_tail_exists_positiveUpper_pairedComplement` | identifies the external contamination exactly.  In the live singleton-positive profile the restoration support contains the selected target's positive tail, so each of the paired packing's two excluded faces lies in that target's positive upper face.  Any family containing both selected targets therefore covers the complete packing complement, and its full upper union satisfies `U\P=range\P`.  The critical wrapper selects those two targets inside the complete non-root family and gives `2|U\P|=w_v+w_u`.  Thus no further mass can be created outside the paired near-tiling: the remaining global problem is precisely to upper-bound `U∩P` (or equivalently force excessive internal occupancy) while using `16W≤(|F|+2)|U|` and the critical quarter-star constraints. |
| `G1PositiveUpperPairedOccupancy.lean`: `univ_sdiff_rootCoarsePairedSubsetUnion`, `four_mul_card_positiveUpper_sdiff_rootCoarse_le`, `three_mul_positiveUpperIncidenceMass_le_four_mul_pairedOccupancyMass`, `two_mul_pairedOccupancyMass_sq_le_intersection_mul_adjacentBudget`, `nine_mul_sum_weight_le_card_add_two_mul_positiveUpperInterPaired`, `genuineDominant_two_tail_exists_positiveUpper_pairedOccupancy` | decomposes the paired packing into eight coarse root-pattern cells.  Its root lower face and two root upper faces contain six cells, so every positive upper face places at least three quarters of its incidence mass inside the paired packing.  Restricting the sharp second moment to that intersection, deleting adjacent nesting by parity, and cancelling the incidence factor gives `9W≤(|F|+2)|U∩P|`.  The critical wrapper returns this internal bound for the same selected targets as the exact identities `U\P=range\P` and `2|U\P|=w_v+w_u`.  The remaining task is therefore an aggregate multiplicity/ownership bound within the disjoint lower, root-upper, and directional-fan components of `P`; another exterior-cardinality estimate cannot help. |
| `G1PositiveUpperRootTrace.lean`: `singletonPositive_subset_negativeTail_of_unitImbalance`, `positiveTails_disjoint_of_singleton_unitImbalance`, `two_mul_card_positiveUpper_inter_singletonUpper`, `two_mul_rootPositiveUpperOccupancyMass_eq_incidenceMass`, `critical_two_tail_nonroot_rootPositive_trace_and_occupancy` | resolves the first componentwise ownership ambiguity uniformly.  Applying oriented collision subtraction from any non-root canonical collision back to the unit-imbalance root forces the root's singleton positive tail into the non-root negative tail; the alternative would demand an impossible imbalance drop below zero.  Hence every non-root positive tail avoids that singleton, every positive upper face occupies exactly one half of the root-positive upper component, and the complete family satisfies the exact incidence identity `2T_A=S`.  No no-heavy assumption or finite case split is needed.  The remaining component count only has to control the negative-root and directional-fan pieces. |
| `G1PositiveUpperRootCells.lean`: `not_negativeTail_subset_positiveTail_of_negativeTails_inter`, `four_mul_card_positiveUpper_sdiff_rootCoarse_eq`, `four_mul_card_positiveUpper_inter_rootCoarse_eq_three_mul`, `pairedOccupancyMass_eq_rootCoarse_add_directionalExcess`, `four_mul_pairedOccupancyMass_eq_three_incidence_add_four_directionalExcess`, `critical_two_tail_nonroot_exact_rootCell_occupancy` | makes the entire coarse root-pattern count exact.  Canonical negative tails meet pairwise, so a non-root negative tail contains at least one root-negative coordinate; collision disjointness then prevents its positive tail from containing both.  Together with the singleton trace from the preceding module, every non-root positive upper face has exactly one quarter of its mass in the two directional cells and three quarters in `Q=Lower(supp(r))∪Upper(B_r)∪Upper(A_r)`.  Thus `4T_Q=3S`.  For the full paired packing, Lean separates the remaining incidence exactly as directional-fan excess `E_dir`, giving `4T_P=3S+4E_dir`.  Componentwise ownership is now reduced to bounding reuse in those two fan slices. |
| `G1SingletonRootClosure.lean`: `exists_singletonPositive_coeff_ne_zero_in_every_canonicalCollision`, `commonTouched_of_canonical_singletonPositive_unitImbalance_allLight`, `criticalCommonTouched_of_not_heavy_one_two`, `not_isCriticalGenuineDominantEscapeCollision_of_one_two`, `genuineDominant_two_le_positiveCard_or_three_le_negativeCard`, `critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_largeTail` | closes the entire singleton-positive/two-negative genuine residual.  Root-trace rigidity makes the root singleton coefficient nonzero in every canonical collision: it is `+1` at the root and `-1` everywhere else.  The no-heavy residual makes every half-witness tail-light, and light-witness reconstruction identifies it up to sign with a canonical collision, so the singleton coordinate is touched by every half-witness—contradicting the residual's no-common-touch field.  Thus the directional-fan excess from the preceding module is vacuous in the genuine `(1,2)` branch.  Globally, after the earlier empty-tail and `(1,1)` exclusions, every surviving genuine root satisfies `|A_r|≥2` or `|B_r|≥3`; the roadmap must now work in those large-tail regimes. |
| `G1BalancedCore.lean`: `exists_balanced_canonicalReducedCollision_of_allLight_noCommonTouched`, `exists_balanced_criticalCanonicalReducedCollision_of_noCommon_noHeavy`, `genuineDominant_exists_balanced_criticalCore`, `genuineDominant_balancedRoot_or_balancedSupportGrowth`, `genuineDominant_two_two_or_three_le_negativeCard`, `critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_balancedCore` | extracts a common structural object from both large-tail regimes.  No-heavy makes every half-witness tail-light; failure of common touch specifically at the anchor supplies a witness with anchor coefficient zero, and reconstruction turns it into a balanced canonical collision with `|A|=|B|≥2`.  Strict dominance then says either this balanced core is the root or it is a distinct support-growing collision of at most half the root padding weight.  Canonical orientation also sharpens the surviving root profiles to exactly `(2,2)` or `|B_r|≥3`.  The global critical localization now carries both that root split and the balanced-root/balanced-growth alternative, providing a shared target for the previously separate private-slice and ordered-slice branches. |
| `G1BalancedCoreCrossing.lean`: `balancedCanonical_positive_inter_other_negative`, `balancedCanonical_otherNegative_two_sided_incidence`, `genuineDominant_exists_balancedCore_twoSided_depthTwo`, `critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_balancedCoreDepthTwo` | makes the balanced core operational.  Imbalance zero forces a forward crossing from its positive tail into every other canonical negative tail; canonical negative-tail intersection simultaneously meets its negative tail.  These sides are disjoint, so every other negative tail contains at least two balanced-core support coordinates, one from each side.  If the balanced core is not the dominant root, the generic small-crossing depth theorem gives depth at least two except at root weight two; the genuine fiber bound and `|B_r|≥2` rule that exception out.  Thus the core is either the root or has support growth at least two and `4w_v≤w_r`.  The global localization retains this factor-four alternative together with the two-sided incidence over the complete canonical family. |
| `G1GlobalSupportStarConcentration.lean`: `genuineDominant_all_other_quarterWeight_growth`, `genuineDominant_exists_other_than_other_global`, `genuineDominant_four_mul_crossStarWeight_le_rootWeight_global`, `genuineDominant_all_other_eighthWeight_growth_global`, `critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_globalSupportConcentrated` | globalizes the old two-tail support-star theorem to every genuine residual.  The post-singleton profile gives `|B_r|≥2`, and `2|B_r|<w_r` excludes the only depth-one boundary, so every non-root canonical collision has depth at least two and `4w_v≤w_r`.  Full blocked-signature coverage forces two distinct non-root targets, making `4∣w_r`; strict small crossing then bounds the complete non-root star by `4Σ_{v≠r}w_v≤w_r` and the total family by `4Σ_vw_v≤5w_r`.  Since a second positive-weight target is always present, no non-root member exhausts the quarter budget; exact dyadic depth upgrades every one to depth at least three, support growth at least three, and `8w_v≤w_r`.  This profile-free concentration is now retained by the global critical localization. |
| `G1TwoTwoRootClosure.lean`: `criticalHalfGap_square_le_two_pow_pred`, `not_isCriticalGenuineDominantEscapeCollision_of_two_two`, `genuineDominant_three_le_negativeTailCard`, `critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_threeNegative_globalSupportConcentrated` | closes the complete balanced `(2,2)` root profile without finite enumeration.  Depth-three growth gives `n≥7`, where the logarithmic half-gap satisfies `L²≤2^(n-1)`.  Distinct blocked signatures supply two distinct positive-weight non-root targets; for a four-coordinate root, `w_r=2^(n-4)`, so its crossing star forces `X≥2^(n-3)` and hence `4X≥2^(n-1)`, contradicting strict small crossing `4X<L²`.  Therefore every surviving genuine root has `|B_r|≥3`, while retaining the global one-eighth support-star decay. |
| `G1GlobalDepthDeficit.lean`: `ambientDepth_add_one_le_supportDepth_add_weight`, `genuineDominant_negativeTail_add_sumDepth_le_ambientDepth_mul_nonrootCard`, `genuineDominant_negativeTail_add_nonrootCard_le_crossStarWeight`, `genuineDominant_four_mul_negativeTail_add_nonrootCard_le_rootWeight`, `genuineDominant_rootSupport_add_five_le`, `critical_largeCross_or_commonTouched_or_heavy_or_genuineDominant_globalDepthDeficit` | converts the existing unweighted escape-depth/external-support tax into a weighted family budget.  If `d=n-|supp(r)|`, a non-root target of depth `t` has padding weight `2^(d-t)`, and `(d-t)+1≤2^(d-t)` pays both its unused external depth and one unit of target multiplicity.  Summing gives `|B_r|+#nonroots≤Σ_{v≠r}w_v`; quarter-star concentration yields `4(|B_r|+#nonroots)≤w_r`.  Since the sole surviving profile has `|B_r|≥3` and distinct signatures give at least two nonroots, the power-of-two root weight is at least 32: `|supp(r)|+5≤n` and `32∣w_r`.  The top-level localization retains this depth-deficit package with the global one-eighth decay. |
| `G1LargeNegativeRootClosure.lean`: `two_mul_ambientDepth_sub_supportDepth_le_weight`, `genuineDominant_two_mul_negativeTailCard_le_crossStarWeight`, `square_two_mul_add_depth_lt_four_mul_pow_mul`, `not_isCriticalGenuineDominantEscapeCollision_of_three_le_negativeTail`, `not_isCriticalGenuineDominantEscapeCollision`, `critical_largeCross_or_commonTouched_or_heavy` | closes the sole large-negative-tail genuine residual uniformly.  Exact dyadic padding improves the depth-deficit charge to `2|B_r|≤Σ_{v≠r}w_v`; quarter concentration gives `8|B_r|≤2^d`, where `d=n-|supp(r)|`, hence `|B_r|≤2^(d-3)`.  Canonical orientation gives `|supp(r)|≤2|B_r|` and thus `n≤2|B_r|+d`.  The root star forces `4·2^d·|B_r|` below the half-gap square, but `criticalHalfGap≤n+1` and the uniform arithmetic inequality `(2|B_r|+d+1)^2<4·2^d·|B_r|` for `d≥5` give the reverse strict bound.  Therefore the genuine dominant branch is empty in every dimension.  Critical G1 is now reduced to the explicit large-crossing, common-touch, and heavy-witness alternatives; those remaining alternatives, not a canonical residual profile, are the next global descent task. |
| `G1HeavyWitnessEscape.lean`: `exists_common_omission_of_heavyWitness`, `criticalHeavyOmissionEscape_of_not_commonTouched`, `criticalHeavyOmissionEscape_two_distinct_omissions`, `critical_largeCross_or_commonTouched_or_heavyOmissionEscape` | strengthens the raw heavy branch into a recursive omission-hypergraph object.  If one half-witness `c` has a coefficient at least two, every other half-witness shares an omission with `c`: otherwise witness combination makes it `-c`, contradicting the coefficient lower bound at the heavy coordinate.  Under failure of common touch, each omission `b` of `c` has a witness vanishing at `b`; the transversal property forces that witness through a different omission `a` of `c`.  Thus the heavy root has at least two distinct omissions and carries an avoiding escape at every omission.  The final critical localization is now large crossing, common touch, or this explicit recursive escape package; converting the large-crossing and omission-escape branches into deletion or a critical-range contradiction remains the G1 frontier. |
| `G1FinalDescent.lean`: `CriticalLargeCrossingDeleteStep`, `CriticalHeavyOmissionEscapeDeleteStep`, `criticalRangeDeleteStep_of_finalBranches`, `global_lower_bound_of_finalBranches` | states the two remaining branches at the exact interface consumed by the global induction.  `GlobalRoadmap.lean` now factors out `CriticalRangeDeleteStep`; critical common touch implies it, but a branch may instead construct the half-modulus `(n-1)`-tuple directly.  The final trichotomy plus deletion for large crossing and heavy omission escape gives the complete critical deletion step, and with G2/G3 immediately gives `globalBound n≤N`.  Thus the unconditional Conjecture 1 roadmap is now exactly two G1 deletion statements plus the independently open G2 and G3, with no hidden canonical-profile obligation. |
| `G1WitnessTransversalDescent.lean`: `quotient_valid_of_witness_transversal`, `exists_validTuple_half_of_witness_transversal`, `criticalHeavyOmissionEscape_multiDelete` | generalizes deletion from a single common touched coordinate to an arbitrary witness transversal.  For any retained-coordinate embedding, if every half-witness touches a deleted coordinate, the retained tuple is valid after quotienting by the involution.  The heavy root's omission set is such a transversal; if it has `t` omissions, then `t≥2` and deleting all of them gives a valid `(n+1-t)`-tuple modulo half the modulus.  This is an unconditional descent from the heavy branch, but it is weaker than the one-coordinate step required by the present sharp induction.  The exact remaining heavy task is to recover/pay for the lost `t-1` dimensions using the recursive escapes or additional overlap mass. |
| `G1MinimalTransversalEscape.lean`: `exists_minimalWitnessOmissionTransversal_subset`, `exists_private_witness_of_minimalTransversal`, `exists_external_common_omission_of_minimalTransversal`, `card_le_card_minimalTransversalExternalEscapePairs`, `criticalHeavyMinimalTransversalPackage_of_escape` | shrinks the heavy root omissions to a cardinality-minimal witness transversal `B`.  Every `b∈B` then has a private witness omitting no other point of `B`.  Pairing it with the heavy branch's witness avoiding `b` forces a common omission outside `B`; otherwise witness combination would negate the private witness and contradict the avoiding zero.  The resulting finite external-incidence set projects onto `B`, so it contains at least `|B|` ordered incidences.  The critical package retains `|B|≥2`, valid deletion of all `B` at half modulus, and one counted external private/avoiding escape per deletion vertex.  The next heavy step is to control reuse of the external endpoint and convert this incidence mass into recovered dimensions or a critical-range packing contradiction. |
| `G1GenuineHeavyEscapeIteration.lean`: `critical_largeCross_or_commonTouched_or_genuineHeavyOmissionEscape`, `exists_fresh_common_omission_of_successive_avoidance`, `criticalGenuineHeavyTwoStepEscape_of_omissionEscape`, `critical_largeCross_or_commonTouched_or_genuineHeavyTwoStepEscape`, `global_lower_bound_of_largeCross_and_genuineHeavyTwoStep` | retains the global no-common-touch field that was used to construct, but previously discarded from, the heavy branch.  Every external omission therefore has an avoiding witness.  Two successive avoiding witnesses must share a further omission distinct from the two preceding coordinates; otherwise witness combination makes them negatives, contradicting the second avoiding zero.  Thus every heavy root omission starts a non-backtracking path `b→z→w` through three distinct coordinates.  The exact global interface is upgraded accordingly: large-crossing deletion plus deletion from this genuine two-step heavy escape, together with G2/G3, implies `globalBound n≤N`. |
| `G1AvoidanceGraphCycle.lean`: `exists_witness_zero_at_of_no_commonTouch`, `witnessAvoidanceEdge_extends`, `exists_witnessAvoidanceEdge_cycle`, `criticalGenuineHeavyTwoStepEscape_exists_avoidanceCycle` | turns the iterated heavy escape into a finite recurrence.  Write `x→y` when a half-witness vanishes at `x` and omits `y`.  Under no common touch, every edge extends to `y→z` with `z≠x,y`.  Choosing one extension gives a self-map of the finite directed-edge state space; every orbit repeats, while the non-backtracking identities exclude periods one and two.  Hence the genuine heavy branch contains a directed avoidance cycle of period at least three in every dimension.  The next heavy step is to extract the witnesses around a minimal such cycle and use their coefficient/omission algebra to force common touch, sharp deletion, or enough disjoint overlap mass to pay the multi-deletion deficit. |
| `G1AvoidanceCycleAlgebra.lean`: `exists_witnessAvoidanceExtension`, `witnessAvoidanceBridgeNext_has_doubleOmission`, `exists_witnessAvoidanceBridgeCycle`, `criticalGenuineHeavyTwoStepEscape_exists_bridgeCycle` | retains the coefficient data which created each avoidance successor.  For every edge `x→y`, the chosen extension to `y→z` carries a bridge witness vanishing at `x` and omitting both `y` and `z`, while `z≠x,y`.  The generic finite-orbit argument then gives a periodic bridge orbit of period `d≥3` with a certified local `0,-1,-1` pattern at every iterate.  This replaces the coordinate-only cycle by a uniform cyclic family of half-witnesses on which witness combination and overlap counting can act.  The next heavy milestone is to minimize the period and control additional shared omissions/repeated vertices, yielding either a shortcut, a closed light triangle, or chargeable disjoint mass. |
| `G1MinimalAvoidanceCycle.lean`: `exists_minimalWitnessAvoidanceBridgeCycle`, `minimalWitnessAvoidanceBridgeCycle_iterates_injective`, `minimalWitnessAvoidanceBridgeCycle_period_le_square`, `criticalGenuineHeavyTwoStepEscape_exists_minimalBridgeCycle` | minimizes the positive return time of the witness-labelled successor.  Non-backtracking excludes periods one and two.  Minimality plus the closed-orbit identity makes the first `d` directed edge states pairwise distinct: any earlier collision would turn the index difference into a smaller positive period.  Consequently `3≤d≤m²` for `m` coordinates, and every one of those `d` states retains its `0,-1,-1` bridge witness.  The remaining reuse is now sharply localized: a coordinate may recur only with a different outgoing edge.  The next heavy step is to show such branching gives a shortcut/additional omission incidence, or else obtain a vertex-simple cycle whose witness layers can be counted. |
| `G1AvoidanceCycleBranching.lean`: `witnessAvoidanceSourceBranching_of_not_injective`, `minimalBridgeCycle_period_le_or_sourceBranching`, `criticalGenuineHeavyTwoStepEscape_minimalCycle_small_or_branching` | resolves the first coordinate-reuse split.  If the source map on one minimal period is injective, its period improves to `3≤d≤m`.  Otherwise two distinct edge states have the same source and different targets; their bridge witnesses both vanish at that source.  Witness combination forces either an additional common omission or exact negation.  In the negation branch both witnesses are coefficientwise light, and each edge's omitted target is a `+1` coordinate of the other witness.  Thus all reuse is exposed as either extra omission incidence or a canonicalizable light sign-flip pair.  The next step is to turn those alternatives into a shorter relation/crossing charge, while treating the source-simple cyclic family by direct layer counting. |
| `G1AvoidanceBranchingCanonical.lean`: `exists_nearBalanced_canonicalReducedCollision_of_full_light`, `sourceBranching_commonZeroOmission_or_nearBalancedCanonicalSignFlip`, `criticalGenuineHeavyTwoStepEscape_smallCycle_or_branchingCanonical` | connects the repeated-source branch to the established canonical framework.  A fully light half-witness has anchor coefficient in `{-1,0,1}`; after canonical swap orientation this forces reduced-collision imbalance at most one.  Therefore branching yields either two witnesses with a common zero and a distinct common omission, or one near-balanced canonical collision carrying distinct full coordinates with coefficients `-1` and `+1`.  The exact-negative pair is correctly recognized as one swap orbit, not double-counted as two collisions.  The next heavy step is to expand/count the common-zero rectangle and feed the near-balanced object through the existing cross-or-unit-imbalance transition lemmas. |
| `G1AvoidanceRectangleExpansion.lean`: `commonZeroOmission_triple_or_fork`, `criticalGenuineHeavyTwoStepEscape_smallCycle_or_expandedBranching` | expands the common-zero/common-omission rectangle rather than leaving it as a static pair.  Given witnesses `c,c'` vanishing at `x` and omitting `z`, no common touch supplies `f(z)=0`.  Successive combination with the same `f` produces omissions `w,w'`, both fresh from `x,z`.  If they agree, all three witnesses omit one fresh coordinate; if they differ, `f` has two distinct fresh omissions, one shared with each side.  The critical heavy frontier is now source-simple cycle, triple-common omission, forked double omission, or near-balanced canonical sign flip.  The next step is to iterate/count triple/fork incidence or close it by a short witness combination. |
| `G1AvoidanceNearBalancedTransition.lean`: `nearBalancedCanonicalSignFlip_transitionPackage`, `criticalGenuineHeavyTwoStepEscape_operationalCycleFrontier` | makes the near-balanced sign-flip outcome operational under the retained failure of common touch.  At every negative-tail vertex of its canonical collision, the established attachment theorem supplies a different tail omission and an avoiding witness.  That witness is either heavy, transitions to another canonical collision crossing the source positive tail, or lies in the rigid negative-sign unit-imbalance residual; the last case carries `|B|≥3` and support at least five.  Thus the heavy-cycle analysis rejoins the earlier canonical crossing/support-growth program instead of creating a disconnected residual.  Remaining heavy-side work is the source-simple cycle and triple/fork counting, plus absorbing these operational attachments into a sharp deletion or critical mass contradiction. |
| `G1AvoidanceSourceSimpleCounting.lean`: `minimalBridgeCycle_sourceSimpleLayers`, `criticalGenuineHeavyTwoStepEscape_countedCycleFrontier` | repairs the source-simple branch's information loss.  Instead of retaining only `d≤m`, it keeps the injective source map and proves that its image has cardinality exactly `d`.  The minimal cycle therefore supplies exactly `d` bridge-witness layers with pairwise-distinct zero coordinates, each still omitting its current and next targets.  The critical operational frontier now exposes this counted package directly; repeated sources still feed the triple/fork or near-balanced transition branches.  The next step is to identify the cyclic target permutation and charge these distinct layers to overlap mass or deletion capacity. |
| `G1AvoidanceVertexCycleCounting.lean`: `witnessAvoidanceCycle_state_next_eq_rotate`, `witnessAvoidanceCycleTarget_eq_source_rotate`, `minimalBridgeCycle_vertexSimpleCycleLayers`, `criticalGenuineHeavyTwoStepEscape_vertexCycleFrontier` | identifies the exact cyclic geometry of the counted branch.  One bridge successor is rotation of the period index, including the last-to-first wrap, so `target(k)=source(k+1 mod d)`.  Source injectivity therefore implies target injectivity and exactly `d` visited targets.  Rewriting the retained bridge witnesses gives a vertex-simple coordinate cycle `v_k` with coefficient pattern `c_k(v_k)=0`, `c_k(v_(k+1))=c_k(v_(k+2))=-1`.  The next step is to exploit the resulting cyclic omission-incidence matrix—by summing adjacent witnesses, extracting additional omissions, or charging distinct layers to critical overlap/deletion capacity. |
| `G1AvoidanceVertexCycleAlgebra.lean`: `vertexSimpleCycle_twoStepExpansion`, `vertexSimpleCycle_threeOmissions_or_allMidpointClosures`, `criticalGenuineHeavyTwoStepEscape_vertexCycleAlgebraFrontier` | performs the first algebraic expansion of the vertex cycle.  Row `k` omits `v_(k+2)` while row `k+2` vanishes there, so successive avoidance forces another omission shared by those rows.  If it is not the intervening `v_(k+1)`, row `k` has three pairwise-distinct omissions.  Otherwise row `k+2` acquires a backward omission at `v_(k+1)`.  Globally, either some witness has three distinct omissions or every two-step pair satisfies this rigid midpoint closure.  The next step is to reindex the all-midpoint branch into a uniform predecessor/current/successor row profile and combine neighboring rows; the three-omission branch must be charged or expanded rather than merely named. |
| `G1AvoidanceVertexCyclePeriod.lean`: `allMidpointClosures_threeDistinctOmissions_of_four_le`, `vertexCycleAlgebra_period_three_or_threeDistinctOmissions`, `criticalGenuineHeavyTwoStepEscape_vertexCyclePeriodFrontier` | collapses the rigid all-midpoint branch.  At index zero its shifted row omits cyclic offsets `1`, `3`, and `4`; these are pairwise distinct for every `d≥4`, so source injectivity turns them into three distinct omitted coordinates.  Since minimal cycles already satisfy `d≥3`, the entire vertex-simple branch reduces to `d=3` or a three-omission witness.  This removes all longer source-simple periods from the residual classification.  The next step is to feed the exact triangle into the existing triangle algebra and to expand/count the now-unified three-omission outcomes together with the triple/fork branches. |
| `G1AvoidancePeriodThreeTriangle.lean`: `periodThreeVertexCycle_exactTriangle_or_threeDistinctOmissions`, `periodThreeVertexCycle_threeDistinctOmissions_firstEven`, `criticalGenuineHeavyTwoStepEscape_vertexCycleTriangleFrontier` | resolves the period-three graph interface.  Its three rows omit the other two cycle vertices; any further omission gives the three-distinct branch, while absence of further omissions is exactly an omission triangle accepted by `G1Triangle`.  At arbitrary two-adic depth the whole source-simple residual is therefore “exact triangle or three omissions,” with no abstract cycle left.  At first-even depth, odd cofactor gives `¬4∣2q`; the existing exact-triangle theorem plus no common touch then forces three omissions as well.  Next use the higher-depth exact-triangle divisibility/profile machinery, and aggregate all three-omission/triple/fork objects into critical mass or deletion capacity. |
| `G1AvoidanceExactTriangleZero.lean`: `exactOmissionTriangle_zeroOpposite_of_noCommonTouch_zmod`, `exactOmissionTriangle_pureZeroEdge_of_noCommonTouch_zmod`, `criticalGenuineHeavyTwoStepEscape_pureTriangleFrontier` | exploits the higher-depth exact triangle rather than leaving it opaque.  The opposite coefficients lie in `{0,1,2}`; if all were positive, the existing positive-triangle theorem would force common touch.  Thus one opposite is zero.  The zero-opposite purity theorem then makes that edge exactly `-p-q+2e`, with `e` outside the triangle and every other coefficient zero.  Consequently the source-simple branch is now a pure zero triangle edge or a three-omission witness.  Next use the affine identity `2g_e=h+g_p+g_q` and its cyclic companions/divisibility constraints, while aggregating the three-omission/triple/fork outcomes quantitatively. |
| `G1AvoidanceExactTriangleProfiles.lean`: `threeDistinctOmissions_of_lightTriangle_of_noCommonTouch`, `exactOmissionTriangle_profiles_of_noCommonTouch_zmod`, `criticalGenuineHeavyTwoStepEscape_triangleProfileFrontier` | completes the exact-triangle coefficient split at every even cyclic modulus.  A heavy opposite `2` forces the other two to zero; without a `2`, two adjacent `1`s force common touch and a lone `1` forces a three-omission escape.  Therefore, under no common touch, the only exact residual profiles are `(0,0,0)`, `(0,0,2)` up to rotation, or three distinct omissions.  The first two are exactly the profiles already known to force `4∣N` and quarter-layer/pure-center structure.  Next import those structured expansions into the avoidance frontier and charge their extra centers/layers, rather than retaining raw coefficient cases. |
| `G1AvoidanceTriangleQuarterLayers.lean`: `exactTriangleAllZero_quarterOmissionQuartet`, `exactTriangleZeroZeroTwo_quarterPoint`, `criticalGenuineHeavyTwoStepEscape_triangleQuarterFrontier` | imports the structured consequences of the two residual profiles.  All-zero produces three external pairwise-distinct pure centers and four explicit witnesses at a quarter target: one omits the old vertex triple and three omit the three edges of the center triangle.  The `(0,0,2)` profile yields a certified point doubling to the half target.  Thus the source-simple branch now exposes quarter-layer witness geometry, a quarter point, or three omissions.  The next step is to transport the quartet to the quotient/half-modulus collision machinery and determine whether the bare `(0,0,2)` quarter point can be upgraded to comparable witness layers. |
| `G1AvoidanceQuarterTransport.lean`: `witness_map_addMonoidHom`, `WitnessOmissionQuartetAt`, `quarterOmissionQuartet_castsToHalf`, `quarterPoint_castsToHalf`, `quarterOmissionQuartet_castsTo_nextTwoAdicHalf` | transports the new quarter geometry through the canonical quotient `ZMod N → ZMod M` when `N=2M=4K`.  Additive maps preserve the full witness coefficient vector, so the all-zero quarter quartet becomes four exact omission layers at the next half target `K`; in two-adic form this is the preceding target `2^(s-1)q` modulo `2^s q`.  The bare `(0,0,2)` branch currently transports only its quarter point, not a witness.  The all-zero branch therefore supplies recursive half-target witness data one level down, while the next load-bearing step is to connect that quartet to a valid reduced collision family—or prove a direct weighted contradiction upstairs—and separately enrich or eliminate the bare quarter-point branch. |
| `G1AvoidanceZeroZeroTwoQuarter.lean`: `WitnessBalancedPairLayerAt`, `WitnessQuarterPairLayer`, `pureEdges_sum_eq_two_balancedPair`, `exactTriangleZeroZeroTwo_quarterPairLayer`, `quarterPairLayer_castsToHalf`, `criticalGenuineHeavyTwoStepEscape_triangleQuarterWitnessFrontier` | removes the bare quarter-point outcome.  In a `(0,0,2)` exact triangle, the two zero-opposite edges have distinct pure centers; these centers and the heavy edge form a balanced `(+1,+1,-1,-1)` witness at a quarter target, with the heavy edge as its exact omission pair.  The three pure half-edge vectors add coefficientwise to twice this quarter vector.  Reduction modulo the current half preserves the balanced vector and makes it a half-target witness one layer down.  Thus both surviving triangle profiles now provide recursive witness data: four layers in the all-zero case and one exact pair layer in the `(0,0,2)` case.  Validity of the unreduced tuple still does not imply validity after coordinatewise reduction, so the next step is to control the induced zero-relation kernel or charge these transported layers upstairs. |
| `G1QuotientWitnessKernel.lean`: `zsmul_involution_eq_zero_or_self`, `zeroWitness_map_iff_halfWitness_of_ker_eq_zmultiples`, `zmodCastHom_ker_eq_zmultiples`, `zmodCast_zeroWitness_iff_halfWitness`, `validTuple_zmodCast_iff_no_halfWitness` | identifies the reduction obstruction exactly.  For a valid tuple and any additive map with kernel generated by an involution `h`, the mapped tuple's zero witnesses are precisely the original tuple's `h`-witnesses, coefficient for coefficient.  Hence for `ZMod (2M) → ZMod M`, coordinatewise reduction is valid iff there are no original half witnesses.  More generally, after retaining a subtuple, the only zero relations that must be killed are the supported original half witnesses; this is exactly the condition implemented by witness-transversal deletion.  The quarter layers therefore live in a completely described singular quotient, and the next task is quantitative: find a small deletion set meeting its zero-witness kernel while retaining enough of the transported quartet/pair layer, or charge those layers before quotienting. |
| `G1SubtupleWitnessKernel.lean`: `sum_extend_embedding_zero`, `sum_zsmul_extend_embedding_zero`, `witness_extend_embedding_iff`, `validTuple_embedding`, `embeddedZmodCast_zeroWitness_iff_extendedHalfWitness`, `validTuple_embeddedZmodCast_iff_no_supportedHalfWitness` | localizes the exact kernel to every retained coordinate embedding.  Extending coefficients by zero gives an iff between witnesses on the embedded subtuple and supported witnesses on the original tuple; in particular validity is hereditary.  After halving, a zero witness on the retained tuple is exactly an original half witness supported wholly on the retained image.  Thus a deletion set repairs quotient validity iff it hits the support—not merely an arbitrarily chosen presentation—of every half witness.  This is the exact survival interface for the transported quarter layers: the next combinatorial step must select a kernel-hitting deletion while preserving a useful quarter coefficient support, or prove that unavoidable destruction itself supplies sufficient deletion/overlap progress. |
| `G1AvoidanceQuarterPairPivot.lean`: `WitnessZeroZeroTwoQuarterPivotPackage`, `exactTriangleZeroZeroTwo_quarterPairPivot`, `criticalGenuineHeavyTwoStepEscape_triangleQuarterKernelFrontier` | exposes the first support-survival pivot.  In the `(0,0,2)` profile, the heavy opposite vertex `d` has nonzero coefficient in all three triangle half witnesses but coefficient zero in the balanced quarter pair.  Deleting `d` therefore destroys the complete local triangle kernel while preserving the quarter layer.  Global no-common-touch simultaneously supplies another half witness with coefficient zero at `d`, proving that this one deletion cannot yet make the quotient valid and naming the surviving kernel relation explicitly.  The branch is now a concrete iteration problem: keep the quarter pair fixed while hitting the remaining supported half witnesses, or show that every further hit into its four-coordinate support pays enough global deletion/overlap mass. |
| `G1AvoidanceQuarterQuartetPivot.lean`: `WitnessAllZeroQuarterTwoPivotPackage`, `exactTriangleAllZero_quarterTwoPivot`, `exactTriangleAllZero_twoDelete_or_pairAvoider` | gives the parallel support pivot for the all-zero quartet.  Deleting one chosen triangle edge meets all three pure half-edge supports, while the opposite balanced quarter-pair vector is zero at both deleted vertices.  Globally there is an exact dichotomy: if every half witness touches that edge, transversal descent produces a valid `(m-2)`-tuple modulo half the modulus; otherwise an explicit half witness vanishes at both pivots and survives as the next kernel obstruction.  This is the first branch producing an unconditional recursive deletion-or-avoider alternative from the quarter geometry.  The next refinement must retain the surviving quarter witness in the valid output explicitly and iterate the pair-avoider case without losing the padding budget. |
| `G1AvoidanceQuarterQuartetRecursive.lean`: `AdmitsValidTupleWithWitness`, `extend_restrict_embedding_eq_of_zero_off`, `exactTriangleAllZero_recursiveHalfWitness_or_pairAvoider` | completes the semantic recursive output of the all-zero pivot.  When `N=2M=4K`, the successful two-coordinate branch returns one explicit valid `(m-2)`-tuple modulo `M` together with the restricted and transported quarter relation as a witness at its half target `K`; zero-extension proves that this is the same coefficient layer, not an unrelated existential witness.  Otherwise the theorem returns an original half witness vanishing at both pivots.  The all-zero profile is therefore reduced to a genuine smaller G1-shaped instance or a strictly stronger pair-avoidance kernel state.  The remaining work is quantitative iteration of those pair avoiders and integration with the global stratum bound. |
| `G1ProtectedQuarterDescent.lean`: `coefficientSupport`, `WitnessSupportTransversal`, `quarterWitness_supportTransversal_recursive`, `quarterWitness_recursive_or_halfWitness_supported` | abstracts the recursive mechanism away from the triangle presentation.  Any support transversal for the original half-witness family that lies in zero coordinates of a protected quarter vector can be deleted; the retained tuple is explicitly valid modulo half and carries that same vector at the next half target.  Taking every coordinate outside the protected support gives an exact alternative: either a valid recursive tuple exists on the quarter support itself, or an original half witness is supported entirely inside that support.  The open combinatorial core is therefore finite-dimensional but uniform: classify or charge half witnesses trapped in the four- or six-coordinate protected supports, while smaller external transversals give immediate recursive descent. |
| `G1QuarterPairTrappedKernel.lean`: `witness_twice_sub_at_zero`, `coefficientSupport_balancedPairCoeffs`, `exactTriangleZeroZeroTwo_protectedPureEdge_quarterPair`, `exactTriangleZeroZeroTwo_no_halfWitness_supportedOn_quarterPair`, `exactTriangleZeroZeroTwo_recursiveFourTuple` | closes the trapped-support alternative for the `(0,0,2)` profile and now retains the geometry needed by the global descent.  Any half witness confined to the four balanced-pair coordinates produces an admissible nonzero zero witness via `2q-c`, contradicting validity.  The strengthened package records simultaneously that the protected pair has support `{x,y,a,b}` and that the profile's heavy edge is exactly `pureEdgeCoeffs d a b`; the two objects share the negative endpoints.  The earlier kernel theorem and four-coordinate recursive theorem remain compatibility projections. |
| `G1QuarterQuartetTrappedKernel.lean`: `exactTriangleAllZero_protectedPureEdge_quarterPair`, `exactTriangleAllZero_no_halfWitness_supportedOn_quarterPair`, `exactTriangleAllZero_recursiveFourTuple` | closes the protected-support alternative for the all-zero profile and retains an aligned pure edge.  The strengthened package records the protected pair on `{x,d,y,z}` together with `cBD=pureEdgeCoeffs y b d`; the pair therefore protects the edge center `y` and endpoint `d`.  The earlier trapped-kernel and recursive-four-tuple statements remain compatibility projections. |
| `G1MinimalSupportTransversal.lean`: `MinimalWitnessSupportTransversal`, `exists_private_witness_of_minimalSupportTransversal`, `minimalSupportPrivateWitness_injective`, `quarterWitness_minimalExternalSupportDescent`, `exactTriangleZeroZeroTwo_linkedMinimalSupportDescent`, `exactTriangleAllZero_linkedMinimalSupportDescent`, `exactTriangleZeroZeroTwo_minimalSupportDescent`, `exactTriangleAllZero_minimalSupportDescent` | turns the kernel-closed quarter recursion into a dimension-sensitive deletion package.  The full complement of the protected support is shrunk to an inclusion-minimal support transversal `B`; deleting only `B` leaves an explicit valid `(m-|B|)`-tuple at half modulus carrying the same protected quarter witness.  Minimality supplies private witnesses indexed injectively by `B`.  Both exact-profile linked specializations now retain a deliberately aligned pure edge, its exact support geometry, and the actual `B`, allowing unique-hit incidence to survive descent. |
| `G1MinimalSupportEscapeIncidence.lean`: `exists_twice_quarter_coefficientEscape`, `minimalSupportPrivateEscapePairs`, `card_le_card_minimalSupportPrivateEscapePairs`, `minimalSupportPrivateEscape_eq_self_or_external`, `quarterWitness_minimalExternalSupportEscapeIncidences` | converts every private deletion witness into a finite coefficient-floor escape.  For the private witness `c_b`, the vector `2q-c_b` is nonzero because `q(b)=0≠c_b(b)`; if all its coefficients were at least `-1`, it would be a forbidden zero witness.  Hence some `i` satisfies `c_b(i)≥2q(i)+2`.  Ordered escape incidences `(b,i)` project onto all of `B`, so their cardinality is at least `|B|`, and private support forces every such `i` either to equal `b` or to lie outside `B`.  The global numerical task is now explicit: charge self-escapes and external escapes to the available collision overlap/padding mass. |
| `G1MinimalSupportCollisionCharge.lean`: `minimalSupportPrivateReducedCollision`, `minimalSupportPrivateReducedCollision_injective`, `minimalSupportPrivateReducedCollision_paddingDepth`, `minimalSupportPrivateCollision_charge_le_overlap`, `minimalSupportPrivateEscape_eq_anchor_or_mem_exactOmissions` | supplies the first exponential charge for the minimal deletion size.  In the no-tail-heavy branch, every private half witness is exactly a reduced collision coefficient vector, and distinct deleted coordinates give distinct shapes.  The shape at `b` omits every other deleted coordinate from its tail support; after allowing for `b` and the distinguished anchor, its exact padding depth is at least `|B|-2`.  Summing these disjoint reduced-shape fibers gives `|B|·2^(|B|-2) ≤ |subsetSumRange(g) ∩ subsetSumShiftRange(g,h)|`.  The coefficient-floor escapes are simultaneously localized: tail-lightness forces each one to occur either at the anchor or in the exact omission set of the protected quarter layer.  What remains is to combine this exponential lower charge with the critical overlap/crossing upper budgets strongly enough to force a singleton deletion or another already-closable G1 branch. |
| `G1MinimalSupportCrossingCharge.lean`: `canonicalizeReducedCollision`, `minimalSupportPrivateWitness_ne_neg`, `minimalSupportPrivateReducedCollision_ne_swap`, `minimalSupportPrivateCanonicalCollision_injective`, `minimalSupportPrivate_crossingCharge` | routes the private-padding charge into the existing large-crossing quantity.  Every private reduced collision is canonically oriented within its swap pair.  Private support proves that no two selected coefficient vectors are negatives, so canonicalization preserves their injective indexing by `B` and their weights.  The selected canonical family has `|B|` members, each of weight at least `2^(|B|-2)`.  Applying the dense canonical crossing theorem to its ordered off-diagonal pairs yields `|B|(|B|-1)·2^(2(|B|-2)) ≤ 2·canonicalCrossMass`.  Thus any non-singleton minimal support deletion now pays directly into the same crossing budget used by the critical large-crossing branch; the remaining task is the numerical comparison with `criticalHalfGap²` and the residual small-`B` cases. |
| `G1MinimalSupportCriticalCrossing.lean`: `pow_add_one_square_le_two_mul_privateCrossCharge`, `critical_minimalSupportPrivate_crossingCharge`, `critical_largeCross_of_minimalSupport_depth_add_two_le_card`, `critical_largeCross_or_minimalSupport_card_le_depth_add_one` | performs the critical numerical comparison.  Write `d=min(s+1,log₂(n+1))-1`.  If `d+2≤|B|`, then `(2^d+1)^2` is at most twice the private crossing charge, so `criticalHalfGap²≤4·criticalCanonicalCrossMass` and the established large-crossing branch fires.  Unconditionally, every all-tail-light minimal support transversal therefore satisfies the exact alternative: large crossing, or `|B|≤d+1`.  Arbitrarily large dimension loss is eliminated from the small-crossing residual; only logarithmically bounded minimal transversals remain to be analyzed. |
| `G1MinimalSupportEscapeFiber.lean`: `minimalSupportPrivateEscapeCoordinate`, `minimalSupportPrivateEscapeCoordinate_mem_anchor_insert_omissions`, `minimalSupportPrivateEscapeFiber`, `exists_large_minimalSupportPrivateEscapeFiber` | concentrates the logarithmically bounded residual without finite enumeration.  Select one certified coefficient-floor escape for each private witness.  Tail-lightness and exact quarter omissions force every selected coordinate into the anchor plus the omission set.  When the protected layer is a balanced pair, that target has at most three coordinates, so a finite pigeonhole argument produces one anchor/omission coordinate whose escape fiber contains at least `⌊|B|/3⌋` private layers.  The next refinement is to split an omission fiber by coefficient `0` versus `+1` (or isolate the anchor fiber), creating a uniform signature class for a sharper crossing/common-touch argument. |
| `G1MinimalSupportEscapeSignature.lean`: `minimalSupportPrivateEscapeCoefficient_eq_zero_or_one`, `minimalSupportPrivateEscapeSignatureFiber`, `exists_large_minimalSupportPrivateEscapeSignatureFiber`, `large_anchor_or_omission_signatureFiber` | refines a concentrated non-anchor omission fiber into exact coefficient signatures.  Exact omission gives `q(z)=-1`; the escape floor gives `0≤c_b(z)`, and tail-lightness gives `c_b(z)≤1`.  A second pigeonhole split therefore retains at least half the fiber at one coefficient in `{0,1}`.  Combined with the preceding one-third concentration, the residual has a uniform alternative: an anchor fiber of size at least `⌊|B|/3⌋`, or a common non-anchor omission and common coefficient carried by at least `⌊⌊|B|/3⌋/2⌋` private layers.  The next step must convert one of these repeated signatures into common touch, heaviness, or additional crossing multiplicity. |
| `G1MinimalSupportSignaturePadding.lean`: `exactOmission_not_mem_minimalSupportDeletion`, `minimalSupportPrivateOneSignature_mem_positiveTail`, `minimalSupportPrivateZeroSignature_paddingDepth`, `minimalSupportPrivateZeroSignature_charge_le_overlap`, `minimalSupportPrivateZeroSignature_crossingCharge` | extracts the first quantitative gain from a repeated exact signature.  An exact quarter omission is outside `B`.  In the coefficient-zero class it is also absent from every private reduced support, so the padding depth improves from `|B|-2` to `|B|-1`; a class of size `k` contributes `k·2^(|B|-1)` to overlap and `k(k-1)·2^(2(|B|-1))` to twice the canonical crossing mass.  The coefficient-one class is recorded as a sunflower whose raw private collisions all contain the same positive-tail coordinate.  The residual task is now split cleanly between the enhanced zero-signature charge, the common-positive `+1` sunflower, and the repeated anchor fiber. |
| `G1MinimalSupportSignatureCritical.lean`: `pow_add_one_square_le_two_mul_zeroSignatureCrossCharge`, `critical_minimalSupportPrivateZeroSignature_crossingCharge`, `critical_largeCross_of_large_zeroSignature_of_depth_add_one_le_card`, `critical_largeCross_or_large_anchor_or_oneSignature_of_depth_add_one_le_card` | specializes the extra zero-signature padding bit to the critical gap.  A zero class with two members dominates `(2^d+1)^2` already when `d+1≤|B|`, one layer earlier than the generic `d+2≤|B|` cutoff.  Since the one-sixth signature class has at least two members for `|B|≥12`, the top bounded-support layer now has only three outcomes: critical large crossing, an anchor fiber of size at least `⌊|B|/3⌋`, or a non-anchor `+1` sunflower of size at least `⌊⌊|B|/3⌋/2⌋`.  The zero-signature alternative is completely eliminated there; the anchor and common-positive branches are the next structural targets. |
| `G1ZeroZeroTwoPureStar.lean`: `pureEdgeCoeffs_ne_zero_mem`, `exists_zeroZeroTwo_pureEdgeCanonical_weight`, `critical_largeCross_of_zeroZeroTwo_minimalSupport_card_eight_le` | uses the concrete heavy edge of the `(0,0,2)` triangle as a fixed crossing-star center.  Its coefficient vector is a pure edge supported on three displayed full coordinates, so tail-light reduction and canonicalization give weight at least `2^(n-3)`.  The original closure used `|B|≥8` both to obtain a second private shape and to infer `n≥7`; the following profile-independent module separates those two roles and sharpens the conclusion. |
| `G1AllZeroPureStar.lean`: `exists_exactPairTwo_pureEdgeCanonical_weight`, `exists_allZero_pureEdgeCanonical_weight`, `critical_largeCross_of_highWeightCanonical_and_minimalSupport_card_two_le_of_seven_le`, `critical_largeCross_or_zeroZeroTwo_minimalSupport_card_eq_one_of_seven_le`, `critical_largeCross_or_allZero_minimalSupport_card_eq_one_of_seven_le` | extracts the pure-star argument through a reusable high-weight-root interface and closes the protected kernel sharply from dimension seven onward.  Its all-zero expansion certifies a coefficient-two center on an exact-pair half edge, while the `(0,0,2)` profile already has such a pure edge; either root has canonical weight at least `2^(n-3)`.  Once `n≥7` is supplied directly, only two private shapes are needed to make the crossing star nonempty.  A profile witness also forces every support transversal to be nonempty.  Consequently, in either exact residual profile, critical large crossing holds or the minimal transversal has exactly one element.  In the small-crossing branch this is the required one-coordinate protected deletion, eliminating every multi-coordinate kernel loss in global dimensions `n≥7`; the low-dimensional base range and the separate large-crossing deletion branch remain to be integrated. |
| `G1ProfileSingletonDescent.lean`: `one_le_criticalIndex_of_zeroZeroTwo_profile`, `one_le_criticalIndex_of_allZero_profile`, `critical_largeCross_or_zeroZeroTwo_singletonHalfDescent_of_seven_le`, `critical_largeCross_or_allZero_singletonHalfDescent_of_seven_le`, `critical_largeCross_or_zeroZeroTwo_admitsHalf_of_seven_le`, `critical_largeCross_or_allZero_admitsHalf_of_seven_le` | integrates the singleton transversal conclusion with the earlier existential protected-quarter descent inside the global all-tail-light branch.  Either exact profile forces `4∣2^(s+1)q`, hence `s≥1` for odd `q`; its protected descent may therefore be instantiated with the previous-layer half target `2^(s-1)q`.  The pure-star dichotomy applied to the selected minimal transversal then gives critical large crossing or an `n`-coordinate valid tuple modulo `2^s q`, with the quarter witness retained.  These are strong local endpoints, but the global `AllHalfWitnessesTailLight` premise is incompatible with the genuine-heavy escape path that currently produces the exact profiles; it must be weakened to lightness of only the selected pure root and private family before upstream composition. |
| `G1HeavyLightnessAudit.lean`: `CriticalGenuineHeavyTwoStepEscape.not_allHalfWitnessesTailLight` | records the roadmap correction explicitly: the genuine-heavy package contains a displayed half witness with a tail coefficient at least two, so it refutes global all-tail-lightness.  This prevents the local singleton endpoints from being composed vacuously with that frontier.  The next correct interface is a local split: the selected pure root and private transversal witnesses are tail-light, enabling the star proof, or one of those selected witnesses is itself a structured tail-heavy residual. |
| `G1MinimalSupportLocalLight.lean`: `MinimalSupportPrivateWitnessesTailLight`, `exists_minimalSupportPrivateWitness_tailHeavy_of_not_localLight`, `exists_other_canonicalReducedCollision_of_minimalSupportPrivate_localLight`, `critical_largeCross_of_highWeightCanonical_and_other_of_seven_le`, `critical_largeCross_of_highWeightCanonical_and_minimalSupportPrivate_localLight` | replaces the incompatible global lightness premise by exactly what the pure-star proof consumes.  If the selected private family is locally tail-light and `|B|≥2`, two private witnesses reduce and canonicalize to distinct shapes, so one differs from any prescribed root.  A high-weight root plus that one other canonical collision fires critical large crossing for `n≥7`, even while an unrelated genuine-heavy witness remains present.  If local lightness fails, the module exposes a concrete selected private witness and tail coordinate with coefficient at least two, retaining its private-zero structure for the next heavy residual analysis. |
| `G1ProfilePureEdgeLightSplit.lean`: `WitnessTailHeavyPureEdge`, `WitnessTailHeavyPureEdge.exists_center_tail`, `exists_exactPairTwo_pureEdgeCanonical_weight_or_tailHeavy`, `exists_zeroZeroTwo_pureEdgeCanonical_weight_or_tailHeavy`, `exists_allZero_pureEdgeCanonical_weight_or_tailHeavy` | localizes the second lightness input.  A displayed exact-pair coefficient-two edge is either tail-light, in which case it reduces to a canonical root of weight at least `2^(n-3)`, or it is a structured tail-heavy pure edge.  In the latter case its heavy tail coordinate is proved to equal the edge's unique coefficient-two center, so the residual retains the full three-coordinate vector rather than merely another existential heavy witness.  Both exact triangle profiles instantiate this split without assuming global tail-lightness. |
| `G1ProfileLocalLightDescent.lean`: `ProfilePureEdgeTailHeavyDescentResidual`, `ProfilePrivateTailHeavyDescentResidual`, `critical_largeCross_or_singletonHalfDescent_or_localHeavy_of_rootSplit`, `critical_largeCross_or_zeroZeroTwo_singletonHalfDescent_or_privateHeavy`, `critical_largeCross_or_allZero_singletonHalfDescent_or_privateHeavy` | combines localized lightness splits with protected descent.  Each sharpened exact-profile endpoint now has only three outcomes: crossing, singleton recursion, or private heavy.  For `(0,0,2)`, protected endpoints force the pure center to be the unique transversal hit.  For all-zero, the aligned pair protects the pure center and one endpoint, forcing the other endpoint to be the unique hit.  Thus every tail-heavy selected root is an explicit private witness. |
| `G1ProfilePureEdgePrivateTransfer.lean`: `coefficientSupport_pureEdgeCoeffs`, `ProfilePureEdgeDoubleHitDescentResidual`, `privateTailHeavy_or_pureEdgeDoubleHit_of_pureEdgeTailHeavy` | records the generic support-only transfer: a pure edge is private when it meets `B` once, while an unaligned generic edge may have a double hit.  This diagnostic theorem remains valid, but the exact-profile frontier no longer uses its double-hit residual because the linked protected geometry chooses an aligned root in both profiles. |
| `G1PrivateHeavyEscape.lean`: `ProfilePrivateHeavyEscapeDescentResidual`, `privateHeavyCoordinate_eq_owner_or_external`, `privateCoefficientEscape_eq_owner_or_external`, `privateHeavyEscape_of_privateTailHeavy` | enriches every remaining private-heavy descent by applying validity to `2q-c`.  It retains an explicit coefficient-floor escape `i` with `2q(i)+2≤c(i)`.  Privacy proves independently that both the heavy tail coordinate and `i` equal the private owner or lie outside `B`; neither can hide at another deleted coordinate.  When the owner itself is heavy, the selected escape is chosen to be that owner, so the two incidences coincide exactly.  The protected vector and existing `(n+1-|B|)` recursive tuple remain in the package. |
| `G1PrivateHeavyTransversalShift.lean`: `ProfilePrivateHeavyAvoidanceEscapeDescentResidual`, `exists_privateTransversalShift_of_noCommonTouch`, `ProfilePrivateHeavyAvoidanceEscapeDescentResidual.exists_shift` | retains the no-common-touch hypothesis that reaches every exact-profile private-heavy branch.  An avoiding witness `r` at the private owner must still meet the minimal transversal at a distinct `u`; privacy makes the original heavy witness vanish there.  Thus the residual carries a directed internal shift `r(owner)=0`, `r(u)≠0`, `c(u)=0` inside `B`, alongside the protected descent and heavy/escape coordinates. |
| `G1PrivateHeavyTransversalCycle.lean`: `minimalSupportTransversalShiftTarget`, `minimalSupportTransversalShift_edgePackage`, `exists_bounded_cycle_of_fixedPointFree`, `exists_bounded_eventualCycle_of_fixedPointFree`, `exists_minimalSupportTransversalShiftCycle`, `ProfilePrivateHeavyAvoidanceEscapeDescentResidual.exists_ownerPathToShiftCycle` | globalizes the single shift to every vertex of `B`.  Minimality selects a private witness at each source, no common touch selects an avoiding witness there, and transversality chooses a distinct target where their zero/nonzero incidences cross.  The resulting fixed-point-free self-map has a cycle of length `2≤d≤|B|`; more sharply, the orbit of the actual heavy owner reaches its first repeat within `|B|` steps.  Thus the cycle remains connected to the retained heavy/escape data. |
| `G1PrivateHeavyTransversalSimpleCycle.lean`: `IsMinimalFixedPointFreeCycle`, `exists_minimalFixedPointFreeCycle_of_period`, `minimalFixedPointFreeCycle_iterates_injective`, `MinimalSupportTransversalShiftEdgePackage`, `minimalSupportTransversalShift_twoCyclePackage`, `ProfilePrivateHeavyAvoidanceEscapeDescentResidual.exists_ownerPathToSimpleShiftCycle` | minimizes the positive period reached from the heavy owner.  The resulting cycle is vertex-simple and still satisfies `i+d≤|B|`; formally its live split is `d=2` or `d≥3`.  The two-cycle arm is already a rigid crossed-incidence rectangle: two distinct vertices point back to each other and both carry their private/avoiding witness packages. |
| `G1PrivateHeavyTransversalCommonOmission.lean`: `exists_common_omission_of_witness_ne_zero_zero`, `exists_external_common_omission_of_distinct_minimalSupportPrivateWitnesses`, `minimalSupportTransversalShift_twoCycle_commonOmissions` | turns crossed zero/nonzero incidence into omission growth through witness combination.  Any two distinct private witnesses cannot be exact negatives and therefore share a `-1` coordinate outside all of `B`; the minimal transversal thus carries a complete pairwise family of externally labelled common omissions.  In a shift two-cycle, the avoiding pair also shares an omission away from both cycle vertices. |
| `G1PrivateHeavyTransversalOmissionFibers.lean`: `MinimalSupportDistinctOrderedPair`, `card_minimalSupportDistinctOrderedPair`, `minimalSupportPrivateCommonOmissionLabel`, `minimalSupportPrivateCommonOmissionLabels_disjoint`, `minimalSupportPrivateCommonOmissionFiber_spec`, `minimalSupportPrivateCommonOmission_labelImage_or_largeFiber` | organizes the complete pairwise omission law as a labelled directed graph.  There are exactly `|B|(|B|-1)` ordered distinct pairs, every chosen label lies outside `B`, and every fiber member certifies two private witnesses omitting that label.  For any `L,r` with `Lr<|B|(|B|-1)`, either at least `L` distinct external labels occur or one label is carried by more than `r` ordered pairs. |
| `G1PrivateHeavyTransversalOmissionVertexFibers.lean`: `minimalSupportPrivateOmissionVertices`, `card_minimalSupportPrivateCommonOmissionFiber_le_square_vertices`, `card_minimalSupport_add_commonOmissionLabels_le`, `minimalSupportPrivateCommonOmission_capacity_or_largeVertexFiber` | converts pair fibers to witness fibers and the image arm to ambient dimension.  A label-pair fiber embeds into the square of the vertices whose private witnesses omit that label, while `B` and all external labels fit disjointly among the `m` coordinates.  Thus `Lr<|B|(|B|-1)` yields `|B|+L≤m` or an external coordinate omitted by a vertex fiber of squared size greater than `r`. |
| `G1PrivateHeavyOmissionVertexLightSplit.lean`: `MinimalSupportPrivateOmissionVerticesTailLight`, `minimalSupportPrivateOmissionVertices_tailLight_or_exists_tailHeavy`, `minimalSupportPrivateOmissionCanonicalCollision_injective`, `minimalSupportPrivateOmissionCanonicalCollision_shared_mem` | localizes the light/heavy split to one shared-omission vertex fiber.  Failure gives an explicit private witness in that same fiber with a tail coefficient at least two.  In the light arm the fiber injects into canonical reduced collisions, and a shared non-anchor omission `k.succ` survives canonicalization as membership of one of the two collision sides.  The following charge theorem uses the stronger general canonical-density route; the retained coordinate remains available for finer orientation analysis if the heavy branch requires it. |
| `G1PrivateHeavyOmissionVertexCrossingCharge.lean`: `minimalSupportPrivateOmissionReducedCollision_paddingDepth`, `minimalSupportPrivateOmission_crossingCharge`, `critical_largeCross_of_two_light_privateOmissionVertices`, `critical_privateOmission_capacity_or_largeCross_or_tailHeavy` | gives every locally light member of `V_z` padding weight at least `2^(|B|-2)` and charges all ordered distinct canonical fiber pairs to global crossing mass.  Consequently, at the usual critical depth, just two light vertices force the large-crossing inequality.  Composing with the exact label-fiber count yields three live outcomes: `|B|+L≤n+1`, critical large crossing, or an explicit tail-heavy private member of the selected large shared-omission fiber.  The next task is to turn the capacity arm or multiple fiber-local heavy witnesses into protected deletion/escape progress. |
| `G1PrivateHeavySelectedLightCharge.lean`: `MinimalSupportSelectedPrivateWitnessesTailLight`, `minimalSupportSelectedPrivate_crossingCharge`, `card_minimalSupportPrivateTailLight_add_tailHeavyVertices`, `critical_largeCross_or_allButOne_privateTailHeavy`, `critical_largeCross_or_minimalSupport_card_le_depth_add_one_or_allButOneHeavy` | generalizes the padding/crossing argument from omission fibers to any selected private owners.  Each selected light owner keeps weight `2^(|B|-2)`.  Therefore, at critical depth, two light owners force large crossing.  The light and heavy owners partition `B`, so outside large crossing all but at most one owner is tail-heavy.  Without a depth premise the exact frontier is: large crossing, `|B|≤d+1`, or at least `|B|-1` distinct tail-heavy private owners, where `d=min(s+1,log₂(n+1))-1`.  The next step is to exploit the distinct-owner heavy family through its owner/external heavy and escape coordinates. |
| `G1PrivateHeavyCoordinateFibers.lean`: `minimalSupportPrivateHeavyCoordinate`, `minimalSupportPrivateHeavyCoordinate_eq_owner_or_external`, `card_minimalSupportPrivateSelfHeavy_add_externalHeavyVertices`, `minimalSupportPrivateHeavy_self_or_capacity_or_largeExternalFiber`, `critical_largeCross_or_smallSupport_or_manySelfHeavy_or_capacity_or_largeExternalHeavyFiber` | selects a coefficient-`≥2` tail coordinate for every heavy private owner and uses privacy to split it into the owner itself or an external label.  Exact image/fiber counting yields many self-heavy owners, `|B|+L≤n+1`, or more than `r` distinct private witnesses heavy at one external coordinate whenever `A+Lr` is below the heavy-owner count.  Combined with the all-but-one theorem, the critical frontier has precisely these outcomes after large crossing and small `B`.  Next attach the `2q-c` coefficient-floor escape to every selected owner and exploit repeated heavy/escape locations. |
| `G1PrivateHeavyJointEscapeFibers.lean`: `minimalSupportPrivateHeavyEscapeCoordinate`, `minimalSupportPrivateHeavyEscapeCoordinate_eq_owner_or_external`, `minimalSupportPrivateHeavyEscapeCoordinate_eq_owner_of_selfHeavy`, `minimalSupportPrivateExternalHeavyFiber_ownerEscape_or_capacity_or_largeJointFiber`, `critical_largeCross_or_smallSupport_or_manySelfHeavy_or_capacity_or_jointHeavyEscapeFiber` | selects a `2q-c_b` coefficient-floor escape for every heavy owner while normalizing self-heavy owners to escape at themselves.  Inside a common external-heavy fiber, escape locations split into distinct owners or external labels.  A second exact image/fiber count yields many owner escapes, `|B|+D≤n+1`, or more than `r` private witnesses sharing one external `(heavy,escape)` pair.  The two-stage critical theorem composes this refinement with the preceding heavy-coordinate frontier and retains the protected quarter witness throughout.  Next exploit the joint signature algebraically across distinct private witnesses. |
| `G1PrivateHeavyJointFiberAlgebra.lean`: `exists_coefficient_add_two_le_of_distinct_witnesses`, `exists_minimalSupportPrivateCoefficientGap_eq_targetOwner_or_external`, `minimalSupportPrivateJointExternalHeavyEscapeFiber_pairExpansion` | uses validity on the difference of two same-target witnesses to force a directed coefficient gap of at least two.  For private witnesses its coordinate is the target owner or external to `B`.  Two distinct members of one joint external heavy/escape fiber therefore carry a common external omission and two opposite directed gaps; the gaps are distinct from each other and the omission, while both common heavy and escape coordinates are also distinct from that omission.  Next count target-owner gaps versus external gap labels across a large joint fiber. |
| `G1PrivateHeavyCoefficientGapFibers.lean`: `MinimalSupportSelectedDistinctOrderedPair`, `minimalSupportSelectedPrivateCoefficientGapCoordinate`, `card_minimalSupportSelectedPrivateTargetGap_add_externalGapPairs`, `card_minimalSupportSelectedPrivateTargetGapPairs_le_ownerHeavy_mul_card`, `minimalSupportSelectedPrivate_ownerHeavy_or_capacity_or_largeExternalGapFiber`, `minimalSupportPrivateJointFiber_ownerHeavy_or_capacity_or_largeExternalGapFiber` | labels every ordered distinct selected private pair by a directed coefficient gap.  Target-owner labels inject into owner-heavy targets times sources; external labels are disjoint from `B` and support exact fibers.  Hence `K|S|+Lr<|S|(|S|-1)` forces more than `K` owner-heavy targets, `|B|+L≤m`, or an external gap label on more than `r` ordered pairs.  Passing from a joint heavy/escape fiber to its owner set preserves cardinality, so the bound applies there verbatim; the following module normalizes the owner-heavy arm. |
| `G1PrivateHeavyOwnerNormalization.lean`: `minimalSupportSelectedPrivateOwnerHeavy_mem_tailHeavy_of_ne_zero`, `minimalSupportSelectedPrivateOwnerHeavy_heavy_escape_eq_owner`, `card_minimalSupportSelectedPrivateOwnerHeavyVertices_le_selfHeavy_add_one`, `minimalSupportSelectedPrivate_selfHeavy_or_capacity_or_largeExternalGapFiber`, `minimalSupportPrivateJointFiber_selfHeavy_or_capacity_or_largeExternalGapFiber` | closes the owner-heavy arm left by the directed-gap count.  Every non-anchor target heavy at its own owner is tail-heavy, the heavy-coordinate selector is normalized to that owner, and the protected escape is the owner too.  These targets inject into the global self-heavy family with only the anchor lost, so `|owner-heavy|≤|self-heavy|+1`.  Thus the pair-count alternative now yields `K≤|self-heavy|`, ambient capacity, or a large external directed-gap fiber, including inside every joint heavy/escape fiber; the following modules expand the external arm. |
| `G1PrivateHeavyGapOmissionFibers.lean`: `minimalSupportSelectedPrivateCommonOmissionLabel_ne_externalGap`, `minimalSupportSelectedPrivateExternalGapOmissionFiber_spec`, `minimalSupportSelectedPrivateExternalGapOmission_capacity_or_largeFiber`, `minimalSupportSelectedPrivate_selfHeavy_or_capacity_or_gapOmissionFiber`, `minimalSupportPrivateJointExternalGapOmissionFiber_lifts` | labels every pair in one fixed external directed-gap fiber by a forced common external omission.  The omission differs from the gap coordinate because both coefficients equal `-1` at an omission but differ by at least two at the gap.  Thus `L'r'<|gap fiber|` gives `|B|+1+L'≤m` or a subfiber of size greater than `r'` sharing both distinct external coordinates.  Composing with the normalized pair count leaves self-heavy owners, either capacity tax, or a large `(gap,omission)` fiber.  Canonical lifts from the projected owner set back to the joint heavy/escape fiber prove that its fixed heavy and escape coordinates remain available. |
| `G1PrivateHeavyGapOmissionVertices.lean`: `minimalSupportSelectedPrivateExternalGapOmissionVertices`, `minimalSupportSelectedPrivateExternalGapOmissionVertices_omit`, `two_mul_card_minimalSupportSelectedPrivateExternalGapOmissionFiber_le_sq_vertices`, `minimalSupportSelectedPrivateExternalGapOmission_capacity_or_largeVertices`, `minimalSupportSelectedPrivate_selfHeavy_or_capacity_or_gapOmissionVertices` | passes from the fixed `(gap,omission)` pair fiber to its endpoint owners.  Every endpoint witness omits the same `w`.  An edge and its reverse cannot both lie in the fiber, since the coefficient at the fixed gap cannot rise by at least two in both directions.  Thus edges together with formal reverses inject into the endpoint square, proving `2|P|≤|V|^2`; more than `r` pairs force `2(r+1)≤|V|^2`.  The full two-stage theorem now ends in a quantitatively large private-owner family sharing `w`, while retaining canonical lifts to the joint heavy/escape fiber. |
| `G1PrivateHeavyGapSourceTargetSplit.lean`: `minimalSupportSelectedPrivateGapSourceOmissionVertices`, `minimalSupportSelectedPrivateGapHeavyTargetVertices`, `minimalSupportSelectedPrivateGapSourceOmissionVertices_spec`, `minimalSupportSelectedPrivateGapHeavyTargetVertices_spec`, `card_minimalSupportSelectedPrivateGapSourceOmission_add_heavyTargetVertices_le_endpoints`, `minimalSupportSelectedPrivateGap_manySourceOmissions_or_manyHeavyTargets` | splits every fixed `(gap,omission)` edge by its source coefficient at the gap.  A source coefficient `-1` makes a witness omit both distinct external coordinates; otherwise the witness floor makes the source nonnegative and the gap inequality makes the target coefficient at least two.  These double-omission sources and gap-heavy targets are disjoint endpoint families.  The two edge classes inject respectively into `D×V` and `V×H`, so `(A+C)|V|<|P|` forces more than `A` double-omission sources or more than `C` gap-heavy targets.  Next feed either abundant class into the existing omission-fiber or heavy-coordinate counts while preserving the fixed joint signature. |
| `G1PrivateHeavyJointGapCapacity.lean`: `card_add_three_le_of_three_external`, `minimalSupportPrivateJointOwnerLift_heavy_at_fixed`, `minimalSupportPrivateJointGapSourceOmission_card_add_three_le`, `minimalSupportPrivateJointGapHeavyTarget_eq_fixed_or_card_add_three_le`, `minimalSupportPrivateJointGap_capacity_three_or_manyHeavyAtFixed` | specializes the source/target split back to one joint heavy/escape fiber.  Every lifted witness is heavy at its fixed external coordinate `z`.  A source omitting the selected gap therefore makes `z`, the gap, and the common omission three distinct external coordinates, forcing `|B|+3≤m`.  A gap-heavy target has the same consequence unless its gap equals `z`.  Hence a dense terminal fiber forces this three-coordinate capacity bound or many targets whose directed gap is normalized to the original common heavy coordinate.  Next exploit strict coefficient growth at that fixed common coordinate, whose values are bounded by omission mass. |
| `G1PrivateHeavyJointGapLevels.lean`: `witnessOmissionCoordinates_exact`, `witness_coeff_le_card_witnessOmissionCoordinates`, `card_minimalSupportPrivateJointGapHeavyTargetLevels_le`, `exists_large_minimalSupportPrivateJointGapHeavyTargetLevelFiber`, `exists_fresh_gap_of_distinct_jointHeavyTarget_sameLevel` | makes the coefficient bound behind the normalized branch explicit.  A witness coefficient outside its exact omission set is at most the number of omissions, so the common-heavy coefficient has only the `m` levels `2,…,m+1`.  More than `mr` normalized heavy targets therefore put more than `r` targets at one level.  Any two distinct witnesses in that repeated-level fiber agree at `z` and both omit `w`, so validity forces a new directed gap away from both fixed coordinates; its label is the target owner or external to `B`.  Next count these restarted owner/external gap labels and normalize the owner arm again. |
| `G1PrivateHeavyJointGapFreshFibers.lean`: `card_minimalSupportSelectedPrivateFreshTarget_add_external`, `minimalSupportSelectedPrivateFreshExternal_capacity_or_largeFiber`, `minimalSupportSelectedPrivateFresh_selfHeavy_or_card_add_three_le`, `card_minimalSupportPrivateJointGapHeavyTargetLevelOwners_le_selfHeavy_add_two_or_capacity`, `card_minimalSupportPrivateJointGapHeavyTargetVertices_le_levels_mul_selfHeavy_or_capacity` | supplies a reusable exact counter for directed gaps constrained away from two fixed external coordinates.  Target-owner gaps inject into owner-heavy targets times sources and hence normalize into the global self-heavy family.  External gap labels avoid `B,z,w`, so even one is a third distinct external coordinate and forces `|B|+3≤m+1`.  Instantiating on the cardinality-preserving owner projection of a repeated normalized heavy level closes its entire pair count: outside capacity each level has at most `|self-heavy|+2` owners.  Combining this with the `m` possible levels from 2gn bounds the whole normalized heavy-target family by `m(|self-heavy|+2)`, or returns three-coordinate capacity.  Next substitute this bound into 2gm's source/target threshold and propagate it backward through the earlier fiber counts. |
| `G1PrivateHeavyJointGapClosure.lean`: `minimalSupportPrivateJointGap_dense_card_add_three_le` | substitutes the normalized target bound from the fresh-level closure directly into the joint source/target density theorem.  A fixed `(gap,omission)` fiber satisfying `(A+m(|self-heavy|+2))|V|<|P|` must obey `|B|+3≤m+1`: otherwise 2gm normalizes the gap and produces more than `m(|self-heavy|+2)` heavy targets, contradicting the 2go bound.  Thus the normalized joint-gap terminal branch is eliminated rather than renamed.  Next derive this density premise from the upstream edge/vertex and omission-fiber counts with explicit global thresholds. |
| `G1PrivateHeavyJointGapBackprop.lean`: `minimalSupportPrivateJointExternalGap_dense_card_add_three_le`, `card_minimalSupportPrivateJointExternalHeavyEscapeOwners_le_selfHeavy_or_capacity` | propagates the dense closure through both upstream label counts.  An external-gap fiber larger than `2m(|self-heavy|+2)|S|` either pays two omission labels or contains a joint `(gap,omission)` fiber dense enough for the preceding closure; both force `|B|+3≤m+1`.  Feeding this into the normalized all-pairs gap count with three external labels and owner threshold `|self-heavy|+1` yields, outside capacity, `|S|≤|self-heavy|+6m(|self-heavy|+2)+2` for every joint heavy/escape owner family.  Next push this explicit joint-fiber bound backward through the escape-coordinate and heavy-coordinate counts. |
| `G1PrivateHeavyExternalHeavyBound.lean`: `minimalSupportPrivateExternalHeavyOwnerEscape_ownerHeavy`, `card_minimalSupportPrivateExternalHeavyOwnerEscapeVertices_le_selfHeavy_add_one`, `card_minimalSupportPrivateExternalHeavyFiber_le_selfHeavy_or_capacity` | closes both arms of the escape-coordinate split quantitatively.  Because the protected witness vanishes on `B`, escape at the owner forces its private coefficient there to be at least two; all non-anchor owner escapes inject into the global self-heavy family.  Combining the resulting `|owner escapes|≤|self-heavy|+1` with three escape labels and the 2gq joint-fiber bound gives, outside `|B|+3≤m+1`, `|external-heavy fiber|≤H+1+3(H+6m(H+2)+2)` where `H=|self-heavy|`.  Next propagate this fixed-fiber bound through the heavy-coordinate label count to control all private tail-heavy owners. |
| `G1PrivateHeavyTailHeavyBound.lean`: `card_minimalSupportPrivateTailHeavyVertices_le_selfHeavy_or_capacity` | propagates the uniform fixed-fiber estimate through the original heavy-coordinate partition.  Setting the self-heavy threshold to its exact cardinality eliminates that branch; three external labels either force `|B|+3≤m+1` or produce a fiber contradicting the preceding bound.  Thus, with `H=|self-heavy|`, `J=H+6m(H+2)+2`, and `F=H+1+3J`, the entire private tail-heavy population satisfies `|tail-heavy|≤H+3F` outside capacity.  All lower escape/gap structure is now compressed into the one global self-heavy family; the next task is to exploit the normalized owner-heavy equations to control that family strongly enough for critical deletion. |
| `G1PrivateHeavySelfHeavyCapacity.lean`: `minimalSupportPrivateSelfHeavy_ownerHeavy`, `minimalSupportPrivateSelfHeavy_omissions_subset_compl`, `two_le_card_minimalSupportPrivateSelfHeavy_omissions`, `minimalSupportPrivateSelfHeavy_exactPair_of_compl_eq_pair`, `minimalSupportPrivateSelfHeavy_pair_commonTouched_or_capacity`, `card_minimalSupportPrivateSelfHeavyVertices_le_one_or_capacity`, `card_minimalSupportPrivateSelfHeavyVertices_le_one_or_capacity_zmod` | begins the genuinely global analysis of the terminal self-heavy family.  Privacy puts every omission outside `B`, while owner heaviness forces at least two omissions.  If fewer than three external coordinates are available, every self-heavy witness has the same exact omission pair and is exactly concentrated with coefficient two at its owner.  Two distinct owners therefore have equal doubles; uniqueness of the nonzero involution forces common touch.  Under the residual's no-common-touch hypothesis this proves `|self-heavy|≤1` or `|B|+3≤m+1`, including the cyclic half-modulus specialization.  The next step is to retain the full pairwise-intersecting family of omission sets in the capacity arm, split off the exact-two layer, and convert its star/triangle structure or the higher-omission mass into crossing/deletion currency. |
| `G1PrivateHeavySelfHeavyOmissionPairs.lean`: `minimalSupportPrivateSelfHeavyExactTwoVertices`, `minimalSupportPrivateSelfHeavyOmissionPairs`, `minimalSupportPrivateSelfHeavy_exactPair_of_omissions_eq_pair`, `minimalSupportPrivateSelfHeavy_commonTouched_of_equal_exactTwo_omissions`, `minimalSupportPrivateSelfHeavyOmissionPair_injective`, `card_minimalSupportPrivateSelfHeavyOmissionPairs`, `minimalSupportPrivateSelfHeavyOmissionPairs_card_eq_two_and_disjoint`, `minimalSupportPrivateSelfHeavyOmissionPairs_pairwise_inter` | retains the exact-two part of the self-heavy family as an external finite two-set system.  Exact positive mass concentrates coefficient two at the owner.  Equal omission pairs at distinct owners force equal doubled tuple entries and hence common touch, so under avoidance the owner-to-pair map is injective and the pair family has exactly the owner-layer cardinality.  Witness combination makes every two pairs intersect.  This exposes the classical star/triangle dichotomy as the next reusable global step; its star center can be tested against a witness avoiding that coordinate, while its bounded triangle arm leaves at most three exact-two owners. |
| `G1PrivateHeavySelfHeavyOmissionStar.lean`: `finset_eq_pair_of_card_eq_two_of_mem`, `pairwiseInter_cardTwo_card_le_three_or_common`, `card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_commonOmission` | proves the reusable star-or-triangle theorem for finite two-set systems and pulls it back through the injective owner-to-omission-pair map.  The exact-two self-heavy owner layer has cardinality at most three, or one external coordinate is omitted by every private witness in the layer.  The next step is to select a half witness avoiding this star center; witness combination then forces it to omit each distinct leaf, converting owner multiplicity into one witness's negative mass. |
| `G1PrivateHeavySelfHeavyStarAvoidance.lean`: `supportAvoidingWitnessAt`, `minimalSupportPrivateSelfHeavyStarLeaf`, `minimalSupportPrivateSelfHeavyOmissionPair_eq_center_leaf`, `minimalSupportPrivateSelfHeavyStarLeaf_injective`, `supportAvoidingWitnessAt_starLeaf_eq_neg_one`, `card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_avoidingOmissions`, `card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_avoidingOmissions` | converts the omission star into one witness's coefficient mass.  Each star pair has a unique non-center leaf, and injectivity of the omission-pair map makes the leaf selector injective.  No common touch supplies a witness `r` with `r(z)=0` at the center.  Combination with every star witness forces `r=-1` at its leaf, so `|exact-two self-heavy|≤|omissions(r)|`; alternatively the exact-two layer has at most three members.  Next split this center-avoiding witness into tail-light and heavy cases: the light arm should enter canonical padding/crossing charge, while the heavy arm must feed a normalized heavy-coordinate recurrence rather than lose the accumulated omissions. |
| `G1PrivateHeavySelfHeavyStarLightHeavy.lean`: `card_witnessOmissionCoordinates_le_negativeTail_add_one`, `witnessNegativeTail_eq_right_of_subsetCollisionCoeffs_eq`, `witnessNegativeTail_eq_left_of_subsetCollisionCoeffs_eq_neg`, `card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_avoidingNegativeTail_add_one`, `card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_canonicalSide_or_tailHeavy` | transfers the star charge through the exact local light/heavy split.  At most the anchor is lost when full omissions are restricted to the negative tail.  A tail-light avoiding witness is canonicalized into an actual member of `canonicalReducedCollisions`; according to its sign, all but that possible anchor loss lie on the canonical right or left side.  Otherwise the same center-avoiding witness retains the full omission reservoir and exposes a tail coefficient at least two.  Thus the global alternative is now `|E2|≤3`, a canonical side with `|E2|≤|side|+1`, or a concrete heavy witness still charged by `|E2|≤|O_r|`.  Next feed the canonical side into padding/crossing mass and normalize the heavy coordinate without forgetting its fixed star-leaf omissions. |
| `G1PrivateHeavySelfHeavyCanonicalTail.lean`: `pow_pred_mul_reducedCollisionWeight_le_positiveUpper_card_of_le_right_add_one`, `card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_largeCanonicalNegativeTail_or_tailHeavy` | removes the light branch's sign ambiguity using canonical orientation: `|A_q|≤|B_q|`, so either signed realization from the preceding split yields `|E2|≤|B_q|+1` for one actual canonical collision.  The exact positive-upper-face identity then turns this linear tail charge into exponential group-value mass, `2^(|E2|-1) w_q ≤ |Upper(q)|`.  The alternative remains a concrete center-avoiding tail-heavy witness with the full star omission reservoir.  The light branch now enters the same canonical negative-tail and upper-face language as the global padding/crossing machinery; the next task is to control overlap of this charged face with the critical root/translated layers, while the heavy branch needs fixed-reservoir normalization. |
| `G1PrivateHeavySelfHeavyStarCapacity.lean`: `minimalSupportPrivateSelfHeavyStarLeaves`, `card_minimalSupportPrivateSelfHeavyStarLeaves`, `minimalSupportPrivateSelfHeavyStarLeaves_subset_compl_erase`, `minimalSupportPrivateSelfHeavyStarLeaves_subset_avoidingOmissions`, `card_transversal_add_exactTwoStar_add_one_le`, `card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_transversal_capacity`, `card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_fixedStarReservoir` | retains the star leaves as an actual finite reservoir `L`, not only a cardinality injection.  The leaf map is injective, so `|L|=|E2|`; privacy and the non-center choice give `L⊆(univ\B).erase z`, while witness combination gives `L⊆O_r` for the center-avoiding witness.  Hence every non-triangle star satisfies the sharp ambient constraint `|B|+|E2|+1≤m+1`.  The bundled endpoint returns these exact set inclusions together with either the canonical upper-face charge from 2gy or the concrete tail-heavy coordinate.  This supplies the fixed external omission set needed to normalize the heavy branch without losing its accumulated mass. |
| `G1PrivateHeavySelfHeavyStarHeavyLocation.lean`: `heavyCoordinate_mem_transversal_or_card_add_reservoir_add_two_le`, `minimalSupportPrivateSelfHeavyStar_heavyCoordinate_mem_transversal_or_capacity`, `card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_canonicalFace_or_strongCapacity_or_internalHeavy` | locates the heavy coordinate of the star-avoiding witness without discarding `L`.  Since the center coefficient is zero and every leaf coefficient is `-1`, a coefficient at least two is distinct from `L∪{z}`.  If it is external to `B`, it consumes one additional complement coordinate and forces `|B|+|E2|+2≤m+1`; otherwise it lies in `B`.  The global endpoint is now exactly four-way: `|E2|≤3`, exponential canonical upper-face mass, the stronger capacity inequality, or an internal heavy coordinate in `B` together with the fixed external leaf reservoir.  Next combine that internal coordinate with its canonical private witness and retain the leaf set through the resulting coefficient-gap/omission split. |
| `G1PrivateHeavySelfHeavyStarPrivateComparison.lean`: `card_transversal_add_reservoir_add_two_le_of_fresh_external`, `minimalSupportPrivateSelfHeavyStar_internalHeavy_privateComparison`, `minimalSupportPrivateSelfHeavyStar_privateComparisonOutcome_or_capacity`, `card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_canonicalFace_or_strongCapacity_or_privateComparison` | compares the center-avoiding witness `c`, heavy at an internal coordinate `e∈B`, with the canonical private witness `p_e`.  Equality transfers the entire leaf reservoir to `p_e`, giving `2≤p_e(e)` and `|E2|≤|O(p_e)|`.  Otherwise validity supplies a directed gap `c(i)+2≤p_e(i)`.  Privacy and the fixed reservoir localize `i`: the owner gives `p_e(e)≥4`, the center gives `p_e(z)≥2`, a leaf gives positive incidence `p_e(l)≥1`, and a fresh external coordinate forces `|B|+|E2|+2≤m+1`.  The global theorem substitutes this four-pattern private outcome for the former opaque internal-heavy residual while hoisting the capacity case.  Next absorb the first two patterns into a higher-omission self-heavy layer and count the center-heavy and positive-leaf incidences. |
| `G1PrivateHeavySelfHeavyHigherOmissions.lean`: `minimalSupportPrivateSelfHeavyAtLeastThreeVertices`, `minimalSupportPrivateSelfHeavy_exactTwo_union_atLeastThree`, `card_minimalSupportPrivateSelfHeavyVertices_eq_exactTwo_add_atLeastThree`, `le_two_mul_exactTwo_or_le_two_mul_atLeastThree_of_le_selfHeavy`, `minimalSupportPrivateSelfHeavyStar_privateComparison_ownerHigher_or_center_or_leaf`, `card_minimalSupportPrivateSelfHeavyExactTwoVertices_le_three_or_canonicalFace_or_strongCapacity_or_higherOwner_or_center_or_leaf` | splits the entire self-heavy family exactly and disjointly as `S=E2⊔H3`, where `H3` consists of private witnesses with at least three omissions; hence `|S|=|E2|+|H3|`, and any lower bound `K≤|S|` gives `K≤2|E2|` or `K≤2|H3|`.  In the large-star branch (`|E2|≥4`), both owner-side outputs of the 2hb comparison now construct the same normalized owner in `H3`: reservoir transfer gives at least four omissions, while owner coefficient at least four gives at least four omissions by the general coefficient-mass bound.  The global endpoint replaces those two ad hoc outputs by an actual higher-omission owner; only center-heavy and positive-leaf alternatives remain.  Next count the at-least-three omission incidences over external coordinates and derive a large fixed-omission fiber or capacity. |
| `G1PrivateHeavySelfHeavyHigherOmissionFibers.lean`: `minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidences`, `three_mul_card_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_le_incidences`, `minimalSupportPrivateSelfHeavyAtLeastThreeOmissionLabels_disjoint`, `card_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionIncidenceFiber_eq`, `minimalSupportPrivateSelfHeavyAtLeastThreeOmission_capacity_or_largeFiber`, `minimalSupportPrivateSelfHeavy_exactTwo_or_higherOmission_capacity_or_largeFiber` | counts the full owner/omission incidence relation of `H3`.  Its exact owner-fiber sum is at least `3|H3|`; privacy puts every coordinate label outside `B`, and a fixed-label incidence fiber has exactly the cardinality of the corresponding distinct-owner fiber.  Hence `Lr<3|H3|` forces `|B|+L≤m+1` or an external `z` omitted by more than `r` members of `H3`.  Combined with `S=E2⊔H3`, any upstream `K≤|S|` and `2Lr<3K` now yields `K≤2|E2|`, complement capacity, or a large common-omission higher-owner fiber.  Next exploit two distinct owners in such a fiber: they already share the omission `z`, so validity must force a second common omission or a directed coefficient gap away from `z`. |
| `G1PrivateHeavySelfHeavyHigherDoubleOmissionFibers.lean`: `minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidences`, `two_mul_card_minimalSupportPrivateSelfHeavyAtLeastThreeOmissionFiber_le_residualIncidences`, `minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionLabel_spec`, `card_minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmissionIncidenceFiber_eq`, `minimalSupportPrivateSelfHeavyAtLeastThreeResidualOmission_capacity_or_largeFiber`, `minimalSupportPrivateSelfHeavy_exactTwo_or_higherOmission_capacity_or_doubleFiber` | iterates the omission count inside a fixed fiber `H3(z)`.  Erasing `z` leaves at least two omissions per owner, so the residual incidence family has size at least `2|H3(z)|`; all labels are external and distinct from `z`.  Thus `L'r'<2|H3(z)|` forces `|B|+1+L'≤m+1` or more than `r'` distinct owners sharing two fixed external omissions `z≠w`.  The two-stage global theorem combines this with 2hd: under `K≤|S|`, `2Lr<3K`, and `L'r'<2(r+1)`, one gets a large exact-two layer, either capacity bound, or a large doubly fixed higher-omission fiber.  Next use a third omission when present, while separating the exact-three layer whose positive coefficient mass is rigid enough for coefficient-profile analysis. |
| `G1PrivateHeavySelfHeavyOmissionExtension.lean`: `minimalSupportPrivateSelfHeavyOmissionExtensionIncidences`, `card_sub_mul_card_le_minimalSupportPrivateSelfHeavyOmissionExtensionIncidences`, `minimalSupportPrivateSelfHeavyOmissionExtensionLabel_spec`, `card_minimalSupportPrivateSelfHeavyOmissionExtensionIncidenceFiber_eq`, `minimalSupportPrivateSelfHeavyOmissionExtension_capacity_or_largeFiber` | extracts the dimension-independent recurrence behind the first two omission counts.  For any subfamily `S⊆H3` whose witnesses all omit a fixed set `R`, the residual incidence family after erasing `R` has size at least `(3-|R|)|S|`.  Every new label lies outside both `B` and `R`, and each fixed-label incidence fiber is bijective with the corresponding distinct-owner extension fiber.  Therefore `Lr<(3-|R|)|S|` forces `|B|+|R|+L≤m+1` or more than `r` owners sharing `R∪{z}` for some fresh external `z`.  This is the generic omission-growth step needed for recursive global counting; instantiate it at `|R|=2` to reach a triple-fixed fiber, then split exact-three from at-least-four witnesses. |
| `G1PrivateHeavySelfHeavyTripleOmissionFibers.lean`: `minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners`, `card_minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmissionOwners_eq`, `minimalSupportPrivateSelfHeavyAtLeastThreeTripleOmissionFiber_spec`, `minimalSupportPrivateSelfHeavyAtLeastThreeDoubleOmission_capacity_or_tripleFiber`, `minimalSupportPrivateSelfHeavy_exactTwo_or_higherOmission_capacity_or_tripleFiber` | flattens the nested double fiber into a direct `H3` subfamily without cardinality loss and instantiates the generic recurrence at `R={z,w}`.  Since `z,w` are distinct and external, every owner has at least one residual omission; hence density forces `|B|+2+L''≤m+1` or a large family sharing three pairwise-distinct external omissions.  The composed three-stage endpoint starts from any `K≤|S|` and returns a large exact-two layer, one of three accumulated capacity inequalities, or more than `r''` owners in the triple-fixed family.  Next partition that family into exact-three and at-least-four omissions; classify the exact-three owner coefficient as `2` with one companion `1`, or `3` with no other positive coefficient. |
| `G1PrivateHeavySelfHeavyExactThreeProfiles.lean`: `minimalSupportPrivateSelfHeavy_exactThree_union_atLeastFour`, `card_minimalSupportPrivateSelfHeavyAtLeastThreeVertices_eq_exactThree_add_atLeastFour`, `card_tripleOmissionFiber_eq_exactThree_add_atLeastFour`, `minimalSupportPrivateSelfHeavyTripleExactThreeFiber_heavyShape`, `minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_tripleExactThree_or_tripleAtLeastFour` | partitions `H3` exactly as `E3⊔H4`, and partitions every triple-fixed fiber the same way.  A factor-two alternative transfers any terminal lower bound to one layer.  In `E3(z,w,u)`, the three fixed external labels are the entire omission set, and the positive profile is rigid: either coefficient `3` at the owner and zero elsewhere off the omissions, or coefficient `2` at the owner plus one unique coefficient-`1` companion.  The global endpoint now ends in exact-two, one of three complement-capacity bounds, or a triple-fixed `E3`/`H4` layer.  Next turn the `E3` profiles into affine owner/companion fiber bounds and restart the general omission recurrence on `H4` with baseline four. |
| `G1PrivateHeavySelfHeavyExactThreeAffineFibers.lean`: `minimalSupportPrivateSelfHeavyTriple_pureThree_union_twoOne`, `minimalSupportPrivateSelfHeavyTriplePureThreeOwner_affine`, `existsUnique_minimalSupportPrivateSelfHeavyTripleTwoOne_companion`, `minimalSupportPrivateSelfHeavyTripleTwoOneCompanion_spec`, `card_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_eq_sum_companionFibers`, `minimalSupportPrivateSelfHeavyTripleExactThree_pureOrCapacityOrLargeCompanionFiber` | splits every exact-three triple fiber exactly into pure owner-`3` and owner-`2` plus companion-`1` layers.  Pure owners all solve `3g_e=h+g_z+g_w+g_u`.  In the second layer the companion is globally unique, lies outside `B` and the three omissions, and satisfies `2g_e+g_f=h+g_z+g_w+g_u`.  Grouping by the selected companion is an exact cardinal partition, so density forces complement capacity or many distinct owners sharing one external companion and one affine right-hand side.  The remaining exact-three step is cyclic torsion-aware counting: bound pure fibers via multiplication by three and fixed-companion fibers via doubling. |
| `G1PrivateHeavySelfHeavyExactThreeCyclicBounds.lean`: `card_le_gcd_of_injective_nsmul_eq_const`, `card_minimalSupportPrivateSelfHeavyTriplePureThreeOwners_le_gcd`, `card_minimalSupportPrivateSelfHeavyTripleTwoOneCompanionFiber_le_gcd`, `card_minimalSupportPrivateSelfHeavyTripleTwoOneOwners_le_two_mul_companionLabels`, `card_minimalSupportPrivateSelfHeavyTripleExactThreeFiber_le`, `minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_tripleAtLeastFour` | proves the reusable cyclic fact that an injectively labelled constant fiber of multiplication by `d` has size at most `gcd(|G|,d)`.  Validity transfers this to the two exact-three profiles: the pure owner-`3` layer has at most three members, and every fixed-companion owner-`2` fiber has at most two.  Exact companion-fiber summation and external-label capacity give `|E3(z,w,u)|≤3+2(m+1-|B|)`.  Substitution into the three-stage global endpoint removes the unbounded exact-three branch; only the at-least-four terminal fiber remains structurally open. |
| `G1PrivateHeavySelfHeavyOmissionDegreeExtension.lean`: `minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences`, `card_sub_mul_card_le_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences`, `minimalSupportPrivateSelfHeavyOmissionDegreeExtension_capacity_or_largeFiber`, `card_minimalSupportPrivateSelfHeavyTripleAtLeastFourFiber_le_direct`, `minimalSupportPrivateSelfHeavyAtLeastFourTripleOmission_capacity_or_quadrupleFiber`, `minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_quadrupleFiber` | generalizes omission growth from the hard-coded `H3` subtype to any private self-heavy owner family with supplied degree `q`.  After erasing fixed omissions `R`, it counts at least `(q-|R|)|S|` residual incidences; all labels remain external and fresh, and fixed-label fibers preserve distinct owners exactly.  The actual triple-fixed `H4` layer is flattened without cardinality loss and instantiated at `q=4`, `|R|=3`, producing complement capacity or a quadruple-fixed family.  The composed four-stage endpoint retains the bounded exact-three inequality and leaves only this four-omission recurrence branch unbounded. |
| `G1PrivateHeavySelfHeavyExactDegreeProfiles.lean`: `minimalSupportPrivateSelfHeavy_exactDegree_union_atLeastSuccDegree`, `card_minimalSupportPrivateSelfHeavy_eq_exactDegree_add_atLeastSuccDegree`, `minimalSupportPrivateSelfHeavyExactDegreeProfileKey_mass`, `minimalSupportPrivateSelfHeavyExactDegreeProfile_spec`, `minimalSupportPrivateSelfHeavyExactDegreeProfileKey_affine`, `card_minimalSupportPrivateSelfHeavyExactDegreeWithin_eq_sum_profileFibers`, `minimalSupportPrivateSelfHeavy_quadrupleExactFour_union_atLeastFive`, `minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_quadrupleExactFour_or_atLeastFive` | gives a uniform terminal interface for every omission degree `q`: any degree-at-least-`q` owner family splits exactly into degree `q` and degree at least `q+1`.  An exact owner is encoded by its owner coefficient and an owner-erased companion vector.  The owner level lies in `[2,q]`; the companion vector is nonnegative, vanishes on `B` and the fixed omissions, and has mass `q-ownerLevel`.  The key reconstructs the witness and yields one affine equation in which only the owner varies.  Realized keys partition the exact layer without loss.  Applied to the four-fixed branch, this gives `ExactFour⊔AtLeastFive` and replaces the global opaque quadruple fiber by that structural alternative.  Next count the realized profile keys and apply cyclic scalar-kernel bounds to each fixed-key fiber. |
| `G1PrivateHeavySelfHeavyExactDegreeCyclicBounds.lean`: `card_minimalSupportPrivateSelfHeavyExactDegreeProfileFiber_le_gcd`, `minimalSupportPrivateSelfHeavyExactDegreeProfileComposition_injective`, `card_minimalSupportPrivateSelfHeavyExactDegreeProfiles_le_choose`, `card_minimalSupportPrivateSelfHeavyExactDegreeWithin_le`, `card_minimalSupportPrivateSelfHeavyQuadrupleExactFourOwners_le`, `minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_boundedQuadrupleExactFour_or_atLeastFive` | closes the exact-layer counting problem uniformly in the degree.  Validity makes owner values injective, so a fixed profile with owner level `d` has at most `gcd(N,d)≤d≤q` owners.  Padding the nonnegative companion vector by a dummy coordinate injects all realized keys into weak compositions of mass `q-2` over the free coordinates plus one, giving `|Exact_q(R)|≤q·binom(m+1-(|B|+q)+q-2,q-2)`.  At `q=4` this bounds every four-fixed exact-four family quadratically and upgrades the global endpoint so its only unbounded omission branch has degree at least five.  Next combine this estimate with fresh-omission growth by well-founded induction on the remaining external coordinates. |
| `G1PrivateHeavySelfHeavyHigherDegreeClosure.lean`: `minimalSupportPrivateSelfHeavyHigherDegreeBound`, `card_minimalSupportPrivateSelfHeavyOmissionDegreeExtensionIncidences_eq_sum_freeOwners`, `sub_mul_card_minimalSupportPrivateSelfHeavy_le_sum_extensionOwners`, `card_minimalSupportPrivateSelfHeavyAtLeastDegree_le_higherDegreeBound`, `card_minimalSupportPrivateSelfHeavyAtLeastFourQuadrupleOmissionOwners_le_higherDegreeBound`, `minimalSupportPrivateSelfHeavy_exactTwo_or_capacity_or_boundedExactThree_or_boundedHigherDegree` | closes the entire higher-degree omission chain by induction on the free-coordinate count.  With `E(D,q)=q·binom(D+q-2,q-2)`, the numerical bound satisfies `F(0,q)=E(0,q)` and `F(D+1,q)=E(D+1,q)+(D+1)F(D,q+1)`.  The exact incidence sum over free labels ensures that the at-least-`q+1` layer enters only states with one fewer free coordinate, so termination is structural rather than a fixed-degree cutoff.  Every degree-at-least-`q` family with `q` fixed omissions has size at most `F(D,q)`.  In particular the whole four-fixed family, across all degrees, is bounded by `F(m+1-(|B|+4),4)`, and the four-stage global endpoint is fully numerical with no unbounded omission branch.  The post-proof audit shows that direct substitution cannot close the critical inequality: `F(D,4)` begins `4,17,76,412,2740,21779,201112`, and even forgetting fresh-label order leaves an exponential bound.  Next constrain joint profile realizability across owners using the existing simple transversal cycle and ordered-pair common-omission labels, then reinsert the sharpened bound upstream. |
| `G1PrivateHeavyRootedOmissionStar.lean`: `minimalSupportPrivateCommonOmissionRowLabel_spec`, `minimalSupportPrivateCommonOmissionRowLabels_subset_rootOmissions`, `card_erase_eq_sum_minimalSupportPrivateCommonOmissionRowFibers`, `minimalSupportPrivateCommonOmission_rootDegree_largeStar`, `minimalSupportPrivateCommonOmission_exactRoot_largeVertexFiber` | begins the cross-owner replacement for the weak 2hn count.  Fixing one private root of omission degree at most `q`, every other selected owner receives a common-omission label lying in the root's own omission set.  The row fibers partition the other owners exactly.  Thus `q·r+2≤|S|` forces an external omission whose full root star has more than `r+1` owners.  On the whole transversal an exact-degree root lands directly in the existing private-omission vertex fiber.  This uses `q`, not the number of free coordinates, and remembers which root generated the shared label.  Next couple these rooted stars along the canonical simple transversal cycle and show that repeated star labels/profiles force common touch, a zero relation, or already-counted crossing mass. |
| `G1PrivateHeavyRootedStarCycle.lean`: `minimalSupportPrivateShiftCycleEdgeLabel_spec`, `card_cycle_eq_sum_minimalSupportPrivateShiftCycleEdgeLabelFibers`, `minimalSupportPrivateShiftCycleVertex_injective`, `card_minimalSupportPrivateShiftCycleEdgeLabelFiber_le_vertices`, `minimalSupportPrivateShiftCycle_capacity_or_largeVertexFiber`, `critical_privateShiftCycle_capacity_or_largeCross_or_tailHeavy` | propagates common-omission labels onto the least-period canonical shift cycle.  Every directed edge is labelled by an external coordinate omitted by both adjacent private witnesses, and the label fibers partition the `d` edges exactly.  Source simplicity makes a fixed edge-label fiber inject linearly into the corresponding omission-vertex fiber, replacing the complete-pair square loss on this structured subfamily.  Thus `L·r<d` gives `|B|+L≤m+1` or one external label omitted by more than `r` distinct private owners.  At critical depth and `r≥1`, the latter yields either large crossing or an explicit tail-heavy owner retaining that label.  Next analyze two edges in one repeated-label fiber: their adjacent private equations and avoiding edge packages must force a zero relation, a stronger shared profile, or a charge to existing crossing mass. |
| `G1PrivateHeavyCycleEdgeAlgebra.lean`: `exists_external_common_omission_private_avoiding_shiftEdge`, `targetPrivate_avoiding_commonOmission_or_neg`, `exists_common_omission_targetPrivate_avoiding_of_tailHeavy`, `targetPrivate_avoiding_commonOmission_eq_target_or_external`, `tailHeavyTargetShiftEdge_threeSharedPackage_or_exactTriangle_or_threeDistinct`, `tailHeavyTargetShiftEdge_threeShared_or_exactTriangle_or_threeDistinct` | supplies the first algebraic layer behind repeated-label control.  On one canonical edge, the source-private and source-avoiding witnesses have a forced external common omission.  The target-private and source-avoiding witnesses either share an omission or are exact negatives; tail-heaviness at the target excludes the negative arm using the avoiding witness's coefficient floor.  Together with the edge label, the three witnesses therefore yield either one omission shared by all three, an exact omission triangle, or a witness with three distinct omissions.  The strengthened package retains the exact endpoint-private and source-avoiding witnesses instead of existentially forgetting them. |
| `G1PrivateHeavyRepeatedCycleEdgeAlgebra.lean`: `minimalSupportPrivateShiftCycleTarget_injective`, `minimalSupportPrivateShiftCycleTarget_eq_vertex_rotate`, `minimalFixedPointFreeCycle_period_le_of_iterate_period`, `minimalSupportPrivateShiftCycle_not_reverse_of_three_le`, `minimalSupportPrivateShiftCycle_repeatedLabelPair_spec`, `three_le_card_minimalSupportPrivateShiftCycleEdgePairEndpointOwners`, `critical_repeatedPrivateShiftCycleLabel_cross_or_twoHeavyEndpoints`, `exists_minimalSupportPrivateShiftCycleIndex_of_mem_edgePairEndpointOwners`, `MinimalSupportPrivateShiftCycleIncomingHeavyEdgeAlgebra`, `minimalSupportPrivateShiftCycle_incomingHeavyEdgeAlgebra`, `MinimalSupportPrivateShiftCycleRepeatedLabelPairedHeavyIncomingEdgeAlgebra`, `critical_repeatedPrivateShiftCycleLabel_cross_or_pairedHeavyIncomingEdgeAlgebra`, `critical_largeRepeatedPrivateShiftCycleLabel_cross_or_pairedHeavyIncomingEdgeAlgebra`, `critical_privateShiftCycle_capacity_or_cross_or_pairedHeavyIncomingEdgeAlgebra`, `critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_pairedHeavyIncomingEdgeAlgebra` | gives a lossless two-edge interface.  For cycle length at least three, two equal-labelled edges touch at least three owners in the same omission fiber; at critical depth they force crossing or contain two heavy owners.  One is retained as the target of a displayed repeated edge.  Every endpoint is assigned a cycle index, inverse rotation identifies its unique incoming edge, and the second distinct heavy owner receives its own fixed-edge shared-omission/exact-triangle/three-omission package.  The cycle pigeonhole is composed back into a global-facing endpoint: `d=2`, complement capacity, critical crossing, or a repeated label carrying the paired heavy incoming-edge algebra.  Next compare the two retained packages coefficient-by-coefficient, beginning with the shared-omission arm, and discharge the explicit two-cycle branch. |
| `G1PrivateHeavyPairedCycleEdgeProfiles.lean`: `MinimalSupportPrivateShiftCycleIncomingEdgeThreeSharedAt`, `MinimalSupportPrivateShiftCycleTargetPurePairAt`, `MinimalSupportPrivateShiftCycleTargetPurePairAt.tailHeavyPureEdge`, `minimalSupportPrivateShiftCycleIncomingHeavyEdgeAlgebra_at_omission`, `MinimalSupportPrivateShiftCyclePairedIncomingEdgesShareRepeatedOmission`, `minimalSupportPrivateShiftCycle_pairedHeavyIncomingEdgeAlgebra_profiles`, `critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_pairedSharedOmission` | performs the first coefficient-profile comparison of both retained incoming edges.  Compare each package's shared omission `x` with the repeated label `z`.  If `x=z`, its source-private, target-private, and source-avoiding witnesses all retain `z`; if `x≠z`, the heavy target has two distinct known omissions and therefore either a third omission or an exact pure coefficient-two edge.  Applying this to both packages routes all non-hard arms to the established exact-triangle, three-omission, or tail-heavy-pure-edge frontiers.  The cycle-count endpoint now leaves only the explicit two-cycle branch or a paired residual in which both canonical incoming-edge triples share `z`.  Next compare the two source-avoiding witnesses and endpoint overlap inside that common-label residual to force a zero relation, common touch, or a bounded shared coefficient profile. |
| `G1PrivateHeavyPairedSharedOmissionAlgebra.lean`: `minimalSupportPrivateShiftCycleIncomingAvoidingWitness`, `MinimalSupportPrivateShiftCycleIncomingAvoidingDirectedGapsAt`, `minimalSupportPrivateShiftCycleIndex_fourPosition_of_mem_edgePairEndpointOwners`, `minimalSupportPrivateShiftCycle_incomingAvoidingWitnesses_eq_or_directedGaps`, `MinimalSupportPrivateShiftCyclePairedSharedAvoidingComparison`, `minimalSupportPrivateShiftCycle_pairedSharedOmission_avoidingComparison`, `critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_pairedSharedAvoidingComparison` | resolves the first algebra inside the paired common-`z` core.  The second heavy target index is one of the four source/target positions of the displayed repeated edges.  The two incoming avoiding witnesses either coincide as a complete coefficient profile or, by validity of the tuple, have coefficient gaps of at least two in both directions.  The two gap coordinates are distinct, neither equals `z`, and each avoids the canonical source at which its upper witness is zero.  The global cycle endpoint retains this exact equality-or-localized-gap alternative.  Next bound reuse of one equal avoiding profile and charge the directed-gap branch to existing crossing/escape fibers; the adjacent and disjoint four-position cases remain explicit. |
| `G1PrivateHeavyAvoidingProfileCyclePacking.lean`: `minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber`, `minimalSupportPrivateShiftCycleIncomingAvoidingWitness_ne_rotate`, `disjoint_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_image_rotate`, `two_mul_card_minimalSupportPrivateShiftCycleIncomingAvoidingWitnessFiber_le`, `MinimalSupportPrivateShiftCyclePairedSharedEqualAvoidingProfile`, `MinimalSupportPrivateShiftCyclePairedSharedDirectedAvoidingGaps`, `minimalSupportPrivateShiftCycle_pairedSharedAvoidingComparison_packedProfile_or_directedGaps`, `critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_packedAvoidingProfile_or_directedGaps` | closes the equal avoiding-profile reuse count on the entire cycle.  One incoming avoiding vector is nonzero at its target, whereas the next incoming vector is zero there as its source; consecutive target indices can therefore never share a profile.  Every fixed-profile fiber is disjoint from its cyclic rotation, giving the dimension-free packing bound `2|fiber|≤d`.  The paired endpoint now retains either a repeated equal-profile fiber of size at least two satisfying this bound, or the localized two-directed-gap package.  Next charge the gap package to the existing private-heavy crossing/escape incidence machinery and determine whether the half-cycle equal-profile bound is strong enough after label/profile summation. |
| `G1PrivateHeavyAvoidingGapCharge.lean`: `canonicalCollisionOfTailLightWitness`, `canonicalCollisionOfTailLightWitness_ne_of_ne_of_commonOmission`, `card_mul_pred_lightWitnessFamily_le_two_mul_canonicalCrossMass_of_commonOmission`, `minimalSupportPrivateShiftCycleIncomingAvoidingLightProfilesAtOmission`, `card_mul_pred_incomingAvoidingLightProfilesAtOmission_le_two_mul_crossMass`, `critical_card_incomingAvoidingLightProfilesAtOmission_lt_halfGap_of_smallCross`, `MinimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt`, `minimalSupportPrivateShiftCycle_incomingAvoidingDirectedGaps_tailHeavy_or_lightProfileCharge`, `MinimalSupportPrivateShiftCyclePairedSharedAvoidingGapCharge`, `critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_packedAvoidingProfile_or_chargedGaps` | gives the sound bridge from avoiding-witness gaps to global G1 counting.  These witnesses are not private, so the private-owner gap fibers do not apply directly.  Instead, every finite tail-light witness family sharing one omission injects into the canonical reduced-collision family: common coefficient `-1` excludes the swap/negation ambiguity.  Hence `|P|(|P|-1)` is at most twice canonical crossing mass.  For cycle profiles, strict critical small crossing implies `|P|<criticalHalfGap`.  The unequal paired branch now retains all localized gaps and yields either a tail-heavy avoiding-witness escape or two distinct members of this charged light-profile family.  Next localize/count the tail-heavy escape and sharpen the combination of profile diversity with the `d/2` equal-profile packing bound. |
| `G1PrivateHeavyAvoidingHeavyEscape.lean`: `tailHeavyWitness_threeDistinctOmissions_or_tailHeavyPureEdge_of_omits`, `minimalSupportPrivateShiftCycleIncomingAvoidingTailHeavyAt_threeDistinctOmissions_or_tailHeavyPureEdge`, `MinimalSupportPrivateShiftCyclePairedSharedLightAvoidingProfileCharge`, `minimalSupportPrivateShiftCycle_pairedSharedAvoidingGapCharge_threeDistinctOmissions_or_tailHeavyPureEdge_or_lightProfileCharge`, `critical_privateShiftCycle_twoCycle_or_capacity_or_cross_or_profiles_or_packedAvoidingProfile_or_lightProfileCharge` | eliminates the tail-heavy avoiding-witness escape rather than merely counting it.  A tail coefficient at least two forces at least two omissions by the coefficient-mass bound.  Together with the retained common omission `z`, a second omission either extends to three distinct omissions or is the exact pair; exact-pair coefficient rigidity then makes the whole witness a tail-heavy pure edge.  Both outcomes were already present in the global frontier.  Consequently the unequal paired-cycle branch is now entirely tail-light and quadratically charged to canonical crossing mass.  Next couple cycle-index multiplicity with profile diversity and the repeated-label partition; multiplying the separate `d/2` and profile-count bounds loses too much. |
| `G1PrivateHeavyTwoCycleClosure.lean`: `critical_minimalSupportPrivateShift_twoCycle_cross_or_threeDistinctOmissions_or_tailHeavyPureEdge`, `critical_privateShiftCycle_capacity_or_cross_or_profiles_or_packedAvoidingProfile_or_lightProfileCharge` | closes the exceptional least-period two-cycle uniformly.  Its two private vertices share an external omission.  If both private witnesses are tail-light, their exact two-owner family forces the critical large-crossing inequality.  If either is tail-heavy, the common omission and the preceding normalization give three distinct omissions or a tail-heavy pure edge.  The global cycle endpoint therefore has no separate length-two branch; only complement capacity, established structural profiles, and the two packed/charged avoiding-profile residuals remain.  Next control repeated transition/profile reuse jointly with the cycle edge-label partition. |
| `G1PrivateHeavyCycleProfileIncidence.lean`: `minimalSupportPrivateShiftCycleIncomingEdgeLabel`, `minimalSupportPrivateShiftCycleLabelledLightProfileIndices`, `minimalSupportPrivateShiftCycle_heavyIndex_labelledLightProfile_or_profiles`, `critical_privateShiftCycle_cross_or_profiles_or_labelledLightProfileIndices_add_one` | replaces the pairwise repeated-edge view by one cycle-wide incidence family.  Every private-heavy cycle vertex is assigned its canonical incoming edge label.  Unless an established exact-triangle, three-omission, or pure-edge frontier occurs, the incoming edge triple shares that label and the incoming avoiding witness is tail-light.  Outside critical large crossing the whole minimal transversal has at most one tail-light private owner, so this labelled light-profile family contains all but at most one of the `d` cycle indices.  This near-spanning family simultaneously retains the index, edge label, and full coefficient profile needed for a joint weighted reuse count.  Next exploit its profile-fiber source zeros to lower-bound canonical padding weight and charge distinct labelled profiles without discarding multiplicity. |
| `G1PrivateHeavyProfileFiberPadding.lean`: `card_incomingAvoidingWitnessFiber_sub_one_le_paddingDepth`, `pow_card_incomingAvoidingWitnessFiber_sub_one_le_canonicalWeight` | converts reuse of one incoming avoiding-witness profile into existing weighted collision currency.  Distinct fiber indices have distinct predecessor/source vertices where the shared profile vanishes.  Removing the possible anchor leaves at least `|fiber|-1` tail zeros, disjoint from the reduced collision support, so its padding depth is at least `|fiber|-1` and its canonical collision weight is at least `2^(|fiber|-1)`.  This is the missing arithmetic obstruction to alternating profile colors.  Next retain these weights in the injection of labelled profiles into canonical collisions and charge weighted off-diagonal profile pairs to crossing mass. |
| `G1PrivateHeavyWeightedProfileCrossing.lean`: `incomingAvoidingLightProfileAtOmissionCanonicalCollision`, `incomingAvoidingLightProfileAtOmissionCanonicalCollision_injective`, `sum_incomingAvoidingLightProfilePairWeights_le_two_mul_crossMass`, `sum_pow_profileFiberPair_le_two_mul_crossMass` | upgrades the common-omission profile injection from an unweighted cardinality bound to an exact weighted charge.  The attached profile off-diagonal maps injectively into canonical distinct collision pairs, preserving each padding weight, so weighted crossing density bounds its full product sum by twice global canonical crossing mass.  Combining termwise with the source-zero theorem charges `sum_{r≠u} 2^(fiber(r)-1)2^(fiber(u)-1)` for every fixed label.  Next combine the label fibers against one global crossing budget and retain the diagonal/single-profile labels. |
| `G1PrivateHeavyCrossLabelProfileBudget.lean`: `minimalSupportPrivateShiftCycleIncomingAvoidingLightProfiles`, `incomingAvoidingLightProfileRawCollision_injective`, `card_witnessOmissionCoordinates_le_two_of_no_threeDistinctOmissions`, `incomingAvoidingLightProfileCommonOmissionPairIncidences`, `card_commonOmissionPairIncidence_rawPairFiber_le_two`, `sum_allRawCollisionOffDiagWeights_le_cross_and_diagonal`, `sum_commonOmissionProfilePairRawWeights_le_cross_and_diagonal`, `sum_commonOmissionProfilePairFiberPowers_le_cross_and_diagonal` | aggregates every common-omission label against one global budget.  After the three-omission frontier is removed, each surviving witness has at most two omissions, so a raw ordered profile pair occurs under at most two labels.  Raw reduction is injective on complete tail-light profiles.  The raw collision off-diagonal is bounded by four times the canonical square, yielding the universal global charge `16*CrossMass + 8*DiagonalMass`; the same bound holds for the source-zero fiber powers.  This replaces the unsound sum of one crossing budget per label by a constant-factor off-diagonal-plus-diagonal budget; the following cycle-cell module embeds the deterministic incidences and retains their diagonal. |
| `G1PrivateHeavyCycleProfileCellBudget.lean`: `minimalSupportPrivateShiftCycleLabelProfileCells`, `card_labelledLightProfileIndices_eq_sum_labelProfileCellCards`, `card_labelProfileCell_le_pow_profileFiber_sub_one`, `sum_reducedCollisionWeightSquare_eq_two_mul_canonical`, `sum_activeLabelProfileCellFiberPowerSquares_le_four_mul_diagonal`, `sum_activeLabelProfilePairCellCards_add_cellCardSquares_le`, `square_card_labelledLightProfileIndices_le_externalCapacity_mul_mass`, `critical_privateShiftCycle_cross_or_profiles_or_cyclePred_mass` | embeds the actual deterministic `(incoming label, complete profile)` cells and proves that their cardinalities partition the retained indices exactly.  Every cell lies in its full cycle profile fiber and is paid by `2^(fiber-1)`.  The active same-label off-diagonal enters the one-budget incidence family, while raw/canonical orbit symmetry charges all active diagonal and single-profile cells by `4*DiagonalMass`.  Cauchy--Schwarz and external-label capacity yield the dimension-free structural estimate `(d-1)^2 <= (m+1-|B|)*(16*CrossMass+12*DiagonalMass)` outside the existing crossing, triangle, three-omission, and pure-edge frontiers.  Next combine this cycle-mass inequality with the established crossing/diagonal dichotomy and dominant-collision branch to obtain a critical-threshold contradiction or deletion. |
| `G1PrivateHeavyDominantCycleCoupling.lean`: `card_labelProfileCellCanonicalFiber_le_four`, `sum_activeLabelProfileCellFiberPowers_le_four_mul_canonicalWeights`, `sum_nonDominantActiveLabelProfileCellFiberPowers_lt_four_mul_weight`, `cycleLength_le_eight_mul_weight_of_strictMajority`, `critical_privateShiftCycle_cross_or_profiles_or_dominantCoupling` | couples the deterministic private-heavy cycle cells directly to the independent maximum-weight collision alternative.  Canonical orientation has two raw preimages and each raw light profile has at most two omission labels, so at most four active cells map to one canonical collision.  In the strict-majority arm, every non-dominant active cell costs less than `4*w(r)` in total and the near-spanning cycle satisfies `d<=8*w(r)`.  The residual retains maximum weight, minimum support, the relative and ambient critical square bounds, and strict majority.  It deliberately does not invoke the older genuine-dominant escape package, whose no-heavy-witness premise is incompatible with this branch.  Next link the private-heavy cycle witnesses to the dominant collision's support/escape geometry and force deletion or a sharper global charge. |
| `G1PrivateHeavyDominantCycleSupportEscape.lean`: `nonDominantLabelProfileCell_exactSupportEscape`, `sum_nonDominantLabelProfileCellFiberPower_mul_dropped_add_power_le_external`, `nonDominantLabelProfileCell_supportEscapeBudget`, `critical_privateShiftCycle_cross_or_profiles_or_dominantSupportEscape` | supplies the first private-heavy-compatible support/escape geometry.  Every non-dominant active cell collision has positive exact support depth from the dominant root, exact dyadic padding normalization, and `|external|=|dropped|+depth`.  Weighting by the source-zero power and summing proves `sum power*|dropped| + sum power <= sum power*|external|`, while retaining `sum power<4*w(r)`.  The critical endpoint now carries this global external-support surplus without assuming that heavy witnesses are absent.  Next analyze the at-most-four dominant-root cells and couple their private/avoiding coefficient data to this non-root external-support charge. |
| `G1PrivateHeavyDominantRootCells.lean`: `dominantRootLabelProfileCell_rawOrientation`, `dominantRootLabelProfileCell_label_zero_or_mem_orientedSide`, `dominantRootIndex_source_zero_and_tailOutsideSupport`, `card_dominantRootIndices_sub_one_le_paddingDepth`, `card_nonDominantIndices_le_sum_cellFiberPowers`, `cycleLength_lt_four_mul_weight_add_paddingDepth_add_two`, `critical_privateShiftCycle_cross_or_profiles_or_dominantRootControl` | resolves the zero-depth root cells jointly.  Their raw profiles are exactly the root or its swap; every tail label lies on the corresponding oriented root side.  More importantly, every root occurrence has a distinct predecessor where the complete avoiding profile vanishes, so all non-anchor predecessors lie outside the root support.  Across both orientations and all labels this proves `|root indices|-1<=n-|supp(r)|` and `2^(|root indices|-1)<=w(r)`.  Combining the exact root/non-root index partition with the non-root `<4*w(r)` budget sharpens the full residual cycle bound to `d<4*w(r)+(n-|supp(r)|)+2`.  Next control reuse of a root-complement coordinate among the weighted non-root external supports and the root predecessor zeros, using the retained private-heavy edge coefficients to force crossing, a structural frontier, or deletion. |
| `G1PrivateHeavyDominantExternalSupportFibers.lean`: `minimalSupportPrivateShiftCycleNonDominantExternalSupportFiber`, `sum_cellPower_mul_externalSupportCard_eq_sum_externalFiberPower`, `nonDominant_supportEscape_capacity_or_largeExternalFiber`, `cycleLength_le_reuse_mul_padding_add_two_or_largeExternalFiber`, `critical_privateShiftCycle_cross_or_profiles_or_dominantExternalFiber` | transposes the non-root weighted external-support sum by coordinates of `Fin n\supp(r)`.  For every threshold `K`, either the support-escape surplus is at most `K*(n-|supp(r)|)` or one explicit root-complement coordinate has fiber mass greater than `K`.  Combining this with the joint root padding and exact root/non-root index partition gives the scale-free operational dichotomy `d<=(K+1)*(n-|supp(r)|)+2` or a displayed high-reuse coordinate.  The critical endpoint retains this alternative inside the private-heavy dominant residual.  Next compare complete avoiding profiles and adjacent private-heavy witnesses inside one high-mass coordinate fiber to bound its multiplicity or charge it to crossing/structural deletion. |
| `G1PrivateHeavyDominantExternalFiberAlgebra.lean`: `canonicalizeReducedCollision_support`, `externalSupportFiber_profileCoeff_eq_one_or_neg_one`, `externalSupportFiber_profiles_eq_or_oppositeAt_or_directedGapsAway`, `card_externalSupportFiber_profileFiber_le_two`, `sum_externalSupportFiberPower_le_two_mul_profilePowers`, `externalSupportDistinctProfiles_oppositeAt_or_directedGapsAway`, `critical_privateShiftCycle_cross_or_profiles_or_dominantExternalProfiles` | starts the coefficient analysis inside one high-reuse root-complement fiber.  Every complete incoming avoiding profile has coefficient exactly `+1` or `-1` at the shared coordinate.  Two profiles are identical, oppositely signed there, or carry mutually directed coefficient gaps at two distinct coordinates away from it.  Outside the three-omission frontier at most two deterministic labels carry one complete profile, so quotienting cells by profile costs only a factor two and preserves high weighted mass.  The critical endpoint now displays a high-mass distinct-profile family with this pairwise algebra.  Next charge the opposite-sign pairs to canonical root-star crossing and the away-gap pairs to the existing avoiding-gap/private-heavy structural machinery, retaining a weighted second moment if first-moment multiplicity is insufficient. |
| `G1PrivateHeavyDominantExternalFiberCharge.lean`: `card_incomingAvoidingLightProfileCanonicalCollisionFiber_le_two`, `externalSupportProfileCanonicalCollision_mem_and_ne`, `sum_externalSupportProfilePowers_le_two_mul_crossStarWeight`, `rootWeight_mul_sum_externalSupportProfilePowers_le_two_mul_crossMass`, `large_externalSupportFiber_mul_rootWeight_lt_four_mul_crossMass`, `cycleLength_le_crossMassDivRoot_add_two_mul_padding`, `critical_privateShiftCycle_cross_or_profiles_or_dominantAdaptiveExternalCapacity` | closes the high-reuse root-complement arm without a separate ordered-pair estimate.  Complete profiles reduce injectively before canonicalization, hence at most the two sign orientations map to one canonical collision.  Because the fixed external coordinate lies outside the root support, every such collision belongs to the punctured dominant crossing star.  Thus `w(r)*profileMass<=2*CrossMass`; including the sharp factor-two label quotient gives `K*w(r)<4*CrossMass` for a cell fiber above `K`.  The adaptive choice `K=floor(4*CrossMass/w(r))+1` is impossible and yields `d<=(4*CrossMass/w(r)+2)*(n-|supp(r)|)+2`; the coarser critical choice `2*criticalHalfGap` gives the previous half-gap bound.  Zero root-padding would force the already closed two-cycle, so every surviving adaptive residual has `1<=n-|supp(r)|`.  The numerical inequalities alone still allow a 3-cycle, so next extract a genuinely structural cycle-length or support-multiplicity lower bound. |
| `G1PrivateHeavyTransversalGlobalProfiles.lean`: `card_minimalSupportTransversalShiftHeavyTargetSources_add_light`, `shiftLightTargetSources_eq_empty_or_singleTargetFiber`, `critical_largeCross_or_allShiftTargetsHeavy_or_singleLightTargetFiber`, `card_transversalAvoidingWitnessFiber_sub_one_le_paddingDepth`, `pow_card_transversalAvoidingWitnessFiber_sub_one_le_canonicalWeight` | corrects the next aggregation scale: the chosen fixed-point-free shift is not known injective, so a periodic component may contain only two vertices and cannot recover `B.card`.  Counting all sources instead gives an exact heavy-target/light-target partition of `B`.  Outside large crossing, the light-target sources are empty or exactly the full indegree fiber over the unique light private owner; hence every missing heavy target is localized in one explicit exceptional fiber.  Reuse of a complete avoiding profile across the full transversal forces distinct source zeros regardless of target collisions, giving padding depth at least `|fiber|-1` and canonical weight at least `2^(|fiber|-1)`.  The source split supplies the heavy target used by the next direct collapse; the global padding estimate remains reusable for later profile fibers. |
| `G1PrivateHeavyTransversalTargetCollapse.lean`: `minimalSupportTransversalShiftEdgeLabel_spec`, `shiftHeavyTargetSource_threeDistinctOmissions_or_tailHeavyPureEdge`, `exists_shiftHeavyTargetSource_of_nonempty_of_light_card_le_one`, `critical_largeCross_or_threeDistinctOmissions_or_tailHeavyPureEdge_of_transversal` | supersedes the planned full-source labelled incidence by a stronger direct collapse.  Every shift edge has an external label omitted by both endpoint private witnesses.  If its target is tail-heavy, that single omission and the general heavy-witness normalization immediately give three distinct omissions or a tail-heavy pure edge.  If all targets were light while there were at most one light owner, applying the fixed-point-free shift twice would fix that owner; hence a nonempty transversal always has a heavy target.  Under the critical depth hypothesis the entire private-target cycle branch is therefore already large crossing, three distinct omissions, or a pure edge, with no cycle length, root choice, or adaptive capacity needed.  Next route the two structural profiles into the existing non-profile/exact-profile deletion interfaces without recreating the private-heavy residual. |
| `G1PrivateHeavyTransversalStructuralProvenance.lean`: `MinimalSupportTransversalShiftTargetThreeOmissionsAt`, `MinimalSupportTransversalShiftTargetPurePairAt`, `shiftHeavyTargetSource_threeOmissionsAt_or_purePairAt`, `MinimalSupportTransversalHeavyTargetStructuralResidual`, `critical_largeCross_or_transversalHeavyTargetStructuralResidual` | retains the data erased by the broad target collapse.  The structural witness is exactly the canonical private witness at `T(b)`; its deterministic external edge label is one named omission.  The three-omission arm keeps two further pairwise-distinct omissions, while the pure arm keeps the exact second omission, tail center, coefficient `2`, and full pure-edge equation.  The critical residual also retains `b`, `T(b)`, `B`, and its minimal-transversal proof and has forgetful maps back to the old broad profiles.  Next pair this residual losslessly with the protected quarter witness, heavy/escape data, and recursive tuple from `ProfilePrivateHeavyAvoidanceEscapeDescentResidual`, splitting off the small-`B` capacity case. |
| `G1PrivateHeavyProtectedStructuralSplit.lean`: `ProfilePrivateHeavyProtectedPayload`, `profilePrivateHeavyAvoidanceEscape_iff_exists_protectedPayload`, `ProfilePrivateHeavySmallTransversalProtectedResidual`, `ProfilePrivateHeavyTargetStructuralProtectedResidual`, `critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetStructural` | rejoins the target provenance to the complete protected descent without losing data.  The named payload contains the quarter witness, disjoint protected transversal, valid `(n+1-|B|)` tuple at half modulus, original private-heavy witness, localized heavy and coefficient-floor escape coordinates, and no-common-touch hypothesis; an iff theorem exactly reconstructs the old residual.  Splitting on critical depth gives `|B|<=min(s+1,log2(n+1))`, large crossing, or the same full payload paired with the canonical target three-omission/pure-edge package.  Both non-crossing outputs forget back to the original residual.  Next derive a monotone support/owner change or direct deletion from the enriched target structural arm, treating the named small-transversal residual separately. |
| `G1PrivateHeavyTargetPureGeometry.lean`: `minimalSupportPrivateWitness_support_inter_eq_singleton`, `minimalSupportTransversalShiftTargetPurePair_owner_or_external`, `minimalSupportTransversalShiftTargetPurePair_card_add_two_le`, `MinimalSupportTransversalHeavyTargetPureGeometryResidual`, `ProfilePrivateHeavyTargetStructuralProtectedResidual.pureGeometry` | extracts the first monotone geometric fact from the retained pure arm.  A canonical private witness meets `B` in exactly its owner.  Since the deterministic edge label `z` is external, the pure target owner is either its coefficient-`2` center or its other omitted endpoint, and the remaining support coordinate is a second external coordinate distinct from `z`; hence `|B|+2<=m+1`.  This refinement is lifted losslessly through the large-transversal structural residual and the complete protected quarter/recursive payload.  Next compare the target pure edge with the retained original private-heavy witness and protected quarter witness to turn the external support pair into a changed owner, a smaller transversal/support, or a deletion; in parallel, attach source avoiders to the named omissions in the three-omission arm. |
| `G1PrivateHeavyTargetPureComparison.lean`: `MinimalSupportTransversalShiftTargetPurePairPrivateComparisonAt`, `minimalSupportTransversalShiftTargetPurePair_privateComparison`, `ProfilePrivateHeavyTargetPureComparisonProtectedResidual`, `critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetPureComparison` | compares the exact pure target with every private witness on the same retained `B`, hence in particular with the original private-heavy witness inside the protected payload.  Different owners force an external common omission which exact purity localizes to one of the two pure endpoints.  Equal owners force literal equality or two oppositely directed coefficient gaps; privacy localizes both gaps to the common owner or outside `B`.  The universal comparison is lifted losslessly to the complete protected payload and substituted into the operational critical split.  Next combine its distinct-owner endpoint omission with the deterministic label/second external coordinate, and normalize the equal-owner equality and bi-gap arms against the retained heavy/escape/quarter inequalities to force descent or a strictly changed potential. |
| `G1PrivateHeavyTargetPureEquality.lean`: `pureEdgeCoeffs_ge_two_eq_center`, `quarterEscape_pureEdge_center_or_externalOmission`, `minimalSupportTransversalShiftTargetPurePair_equalPrivateHeavy` | normalizes the literal-equality arm of the protected pure comparison.  Any coefficient at least two in the exact pure edge is at its unique center, so the payload's heavy coordinate is that center.  If the center is the private owner, the retained owner-coincidence law pins the escape to the same coordinate and the protected quarter coefficient is zero there.  Otherwise the owner is the other omitted endpoint, while the center and escape are external to `B`; an escape away from the center lies outside all three pure support coordinates and has quarter coefficient `-1`.  Next feed these internal-center/external-center alternatives into deletion or a decreasing potential, and normalize the unequal same-owner bi-gap and different-owner endpoint-omission arms. |
| `G1PrivateHeavyTargetPureUnequal.lean`: `coefficientGap_into_pureEdge_eq_center`, `minimalSupportTransversalShiftTargetPurePair_distinctPrivateHeavy` | normalizes every witness distinct from the retained pure target, independent of whether its private owner agrees with the target owner.  A floor-`-1` coefficient gap into a pure edge can occur only at its unique center.  Thus the distinct protected witness has center coefficient `-1` or `0`, its heavy coordinate is not the pure center, and validity supplies a reverse gap at a different coordinate localized to its owner or outside `B`.  If the pure center is that owner, both the moved heavy coordinate and reverse-gap coordinate are external.  Next combine this center-drop/external-rise potential with the equality normalization and the distinct-owner common endpoint omission, aiming for a well-founded iteration or immediate deletion. |
| `G1PrivateHeavyTargetPureNormalizedResidual.lean`: `MinimalSupportTransversalShiftTargetPurePairEqualPrivateHeavyOutcome`, `MinimalSupportTransversalShiftTargetPurePairDistinctPrivateHeavyOutcome`, `ProfilePrivateHeavyTargetPureNormalizedProtectedResidual`, `critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetPureNormalized` | installs the equality and distinct-witness normalizations on the actual private-heavy witness inside the complete protected payload.  The original universal comparison is retained, so the different-owner common endpoint omission is not lost.  The operational critical split now returns small `B`, large crossing, the unchanged target three-omission arm, or a pure arm carrying two-coordinate capacity, the exact owner comparison, and either heavy/escape equality rigidity or center-drop/reverse-gap geometry.  Next define a well-founded potential for the normalized pure arm or derive deletion directly from its internal-center/external-center and drop/rise subcases; the small-`B` and three-omission arms remain independent live tasks. |
| `G1PrivateHeavyTargetPureCenterTransition.lean`: `witness_exists_shared_pureEdge_endpoint`, `tailHeavyWitness_threeDistinctOmissions_or_exactPureEdgeAt_of_omits`, `MinimalSupportTransversalShiftTargetPureCenterChangeAt`, `minimalSupportTransversalShiftTargetPurePair_distinctPrivateHeavy_threeOmissions_or_centerChange` | upgrades the distinct pure-target center drop to an actual structural transition.  Every witness shares an omitted endpoint with a pure target, since otherwise witness combination would make it the target's negative and violate the coefficient floor at the target center.  Retaining that endpoint while normalizing the payload's heavy coordinate yields either three distinct omissions or a second exact pure edge whose center is different from the target center and which shares one old endpoint.  Next lift this dichotomy losslessly into the protected critical residual, then exploit the resulting finite center/endpoint transition graph to force repetition, three omissions, or deletion. |
| `G1PrivateHeavyTargetPureTransitionResidual.lean`: `ProfilePrivateHeavyTargetPureTransitionProtectedResidual`, `ProfilePrivateHeavyTargetPureNormalizedProtectedResidual.transition`, `critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetPureTransition` | installs the exact center-changing alternative on the actual private-heavy payload in the operational critical endpoint.  The lift retains the quarter witness, recursive lower-modulus tuple, transversal, heavy/escape coordinates, pure-target capacity and geometry, and universal owner comparison.  Its pure arm now ends in exact equality rigidity, three omissions for the actual payload witness, or a second pure edge sharing an old endpoint and changing center.  Next build the finite center/endpoint transition relation on these exact pure edges and prove that iteration either reaches the three-omission frontier, repeats incompatibly with validity, or yields a deletable coordinate. |
| `G1PrivateHeavyTargetPureTransitionFresh.lean`: `exactPair_coeffTwo_centers_eq_of_no_common_touched`, `MinimalSupportTransversalShiftTargetPureCenterChangeAt.exists_freshEndpoint`, `MinimalSupportTransversalShiftTargetPureCenterChangeAt.exists_freshEndpoint_zmod` | proves the first transition-graph rigidity.  Under no common touch and uniqueness of the nonzero involution, two coefficient-two witnesses with the same exact omission pair have the same center.  Hence a surviving center-changing transition cannot reuse the old endpoint pair: its non-shared endpoint is outside both old endpoints.  The result is available generically and directly in the critical cyclic modulus.  Next classify pairwise-intersecting exact omission pairs into a common-endpoint star or a triangle, then route the triangle to the exact-profile frontier and analyze the star using the retained owners/quarter escape. |
| `G1PrivateHeavyTargetPureEdgeFamily.lean`: `pairwiseInter_cardTwo_common_or_triangle`, `witnessPureEdgeOmissionPairs`, `witnessPureEdgeOmissionPairs_pairwise_inter`, `witnessPureEdgeOmissionPairs_common_or_exactTriangle` | gives the exact global classification suggested by the transition.  A nonempty pairwise-intersecting family of two-sets either has a common vertex or consists of the three edges of one triangle (possibly a subfamily only in the star case).  Witness combination makes all exact-pair coefficient-two half-witness omission sets pairwise intersect.  Therefore their complete family is an omission star or three actual witnesses form `WitnessExactOmissionTriangle`; the latter is already an established structural frontier.  Next specialize the star center relative to the retained pure target's two external/owner endpoints and use the protected owner comparison plus quarter escape to force deletion or a bounded star arm. |
| `G1PrivateHeavyTargetPureStarCenter.lean`: `MinimalSupportTransversalShiftTargetPureCenterChangeAt.exists_sharedEndpoint_eq_globalStarCenter`, `minimalSupportTransversalShiftTargetPurePair_globalStarCenter_owner_or_external`, `minimalSupportTransversalShiftTargetPureCenterChange_exactTriangle_or_globalStar` | specializes the global pure-edge star to the operational center transition.  Since the old and new edges intersect only at their retained shared endpoint, the global star coordinate equals that endpoint.  The canonical target geometry independently places it at the target owner or outside `B`.  The combined endpoint now returns either the established exact omission triangle or a global star with both facts attached to the exact old/new omission pairs.  Next combine the two star-location cases with the payload owner comparison and quarter escape: an internal star is the target owner, while an external star should either be the deterministic label/quarter omission or force a second external support charge. |
| `G1PrivateHeavyTargetPureStarQuarter.lean`: `minimalSupportTransversalShiftTargetPureCenterChange_globalStar_quarterSplit` | couples the localized global star to the actual protected quarter gap.  A quarter-gap coordinate cannot be omitted by the payload because the quarter witness has coefficient floor `-1`; hence it differs from the star center.  If the star center is internal, privacy forces it to be both the canonical target owner and payload owner, while the payload's new pure center and quarter escape are both external.  If the star is external, it remains distinct from the owner-or-external quarter escape.  Next lift the exact-triangle/internal-star/external-star alternatives into the complete protected critical residual, preserving the existing payload fields. |
| `G1PrivateHeavyTargetPureStarQuarterResidual.lean`: `MinimalSupportTransversalShiftTargetPureStarQuarterOutcome`, `ProfilePrivateHeavyTargetPureStarQuarterProtectedResidual`, `ProfilePrivateHeavyTargetPureTransitionProtectedResidual.starQuarter`, `critical_privateHeavyAvoidanceEscape_smallTransversal_or_largeCross_or_targetPureStarQuarter` | performs the lossless operational lift of the complete pure-edge family classification.  The critical endpoint now retains the original quarter witness, recursive tuple, transversal, capacity, payload, owner comparison, and source provenance while replacing the center-change leaf by an exact omission triangle or a named internal/external global-star outcome.  This exposes the real remaining private-heavy problem directly: turn the two external coordinates in the star arms, or the established triangle frontier, into the required charge/deletion interface. |
| `G1PrivateHeavyTargetPureStarAvoider.lean`: `globalPureEdgeStar_supportAvoider_threeOmissions_or_tailLight`, `globalPureEdgeStar_threeOmissions_or_canonicalAvoider`, `MinimalSupportTransversalShiftTargetPureStarQuarterOutcome.canonicalAvoider` | extracts a general consequence of the global pure-edge star.  The no-common-touch witness chosen to vanish at the star center cannot be a tail-heavy exact pure edge, since the star would force that edge to omit the same coordinate.  Hence it either has three distinct omissions or is tail-light and gives an actual canonical reduced collision, with coefficients equal to the center-avoider up to orientation.  The result attaches that canonical collision to the full internal/external star-quarter outcome without losing its location split.  Next use the avoided star coordinate and the transition leaf/quarter geometry to charge this canonical root into crossing mass or produce deletion. |
| `G1PrivateHeavyTargetPureStarLeafCharge.lean`: `minimalSupportTransversalShiftTargetPureCenterChange_globalStar_avoiderLeaf`, `MinimalSupportTransversalShiftTargetPureStarQuarterCanonicalOutcome.exists_canonicalLeaf` | identifies a forced signed incidence of the canonical star-center avoider.  Witness combination with the center-changing payload makes the avoider omit the payload's non-star leaf.  This leaf differs from both the star center and protected quarter escape, is payload-owner-or-external, and is external in the internal-star case.  The attached canonical collision consequently has coefficient zero at the star center and coefficient `±1` at the forced leaf, while retaining the full internal/external star-quarter split.  Next turn this signed zero/unit pattern into an actual canonical crossing pair or isolate the rigid noncrossing coincidence pattern needed for deletion. |
| `G1PrivateHeavyTargetPureStarLeafTransition.lean`: `PureEdgeStarFreshLeafAt`, `exactPureEdge_leafAvoider_threeOmissions_or_canonicalCross_or_freshLeaf`, `MinimalSupportTransversalShiftTargetPureStarQuarterCanonicalOutcome.threeOmissions_or_canonicalCross_or_freshLeaf` | runs the avoidance argument in the opposite direction at the forced leaf.  The leaf-avoiding witness must omit the global star center.  If tail-light, its canonical collision differs from the center-avoiding collision at the leaf coordinate, so the dense canonical-pair theorem supplies an actual oriented positive/negative crossing.  If tail-heavy, normalization gives three omissions or another exact pure edge through the same star center with a leaf different from the current one.  The operational theorem retains the original canonical root and full star/quarter location package in the fresh-leaf arm.  Finite iteration may cycle rather than grow monotonically; the following module extracts that cycle explicitly. |
| `G1PrivateHeavyTargetPureStarLeafCycle.lean`: `witnessPureEdgeStarLeaves`, `supportAvoidingWitnessAt_eq_neg_one_of_mem_pureEdgeStarLeaves`, `exists_fresh_pureEdgeStarLeaf_of_no_three_of_no_canonicalCross`, `exists_bounded_pureEdgeStarLeafCycle_of_no_three_of_no_canonicalCross` | replaces the informal monotone fresh-leaf picture by the correct finite mechanism.  The center-avoiding witness omits every leaf, so its canonical representative has coefficient `±1` throughout the star-leaf set.  If neither three omissions nor a crossing with this root occurs, each leaf's avoiding witness is another exact pure edge and selects a different leaf.  These choices form a fixed-point-free self-map of the finite leaf set, hence a directed cycle of length between two and the number of leaves, with every cycle edge retaining its exact pure witness. |
| `G1PrivateHeavyTargetPureStarLeafCycleAlgebra.lean`: `minimalFixedPointFreeCycle_apply_iterates_injective`, `PureEdgeStarLeafTransitionAt.exists_center_affine`, `pureEdgeStarLeafCycle_exists_injectiveCenters`, `exists_minimal_pureEdgeStarLeafCycle_with_injectiveCenters` | minimizes the leaf cycle before extracting its algebra.  Every directed edge has a center distinct from the star, source, and successor and satisfies the exact affine recurrence `2g(center_j)=h+g(star)+g(successor_j)`.  The successor leaves are injective around a least-period cycle; validity then forces the selected centers to be injective as well.  Thus the obstruction now contains two equally sized collision-free coordinate families tied by an exact midpoint equation.  Next split according to whether the center image is disjoint from the leaf image: the external case gives direct coordinate capacity, while internal center/leaf incidences must satisfy a cyclic recurrence and are the candidate source of torsion or deletion. |
| `G1PrivateHeavyTargetPureStarLeafCycleCapacity.lean`: `two_mul_add_one_le_of_disjoint_injective_ranges`, `injectiveRanges_capacity_or_intersect`, `pureEdgeStarLeafCycle_capacity_or_internalCenterIncidence`, `exists_minimal_pureEdgeStarLeafCycle_capacity_or_internalCenter` | performs the exact center-image split.  If the injective center and leaf images are disjoint, both avoid the star and therefore occupy `2d+1` distinct ambient coordinates.  Otherwise it displays an internal incidence `center_j=leaf_k`; local pure-edge geometry forces `k!=j` and makes this leaf different from the successor of `j`, while retaining `2g(center_j)=h+g(star)+g(successor_j)`.  The global noncrossing endpoint now returns this capacity-or-internal-incidence dichotomy without discarding the minimized cycle or any center equations.  Next aggregate the internal incidence pattern: sparse incidences should preserve a capacity gain, while a cyclic incidence component should turn the affine recurrences into torsion or a deletion configuration. |
| `G1PrivateHeavyTargetPureStarLeafCycleIncidence.lean`: `card_add_two_le_of_injective_range_and_two_fresh`, `exists_rangeIndexPerm`, `PureEdgeStarLeafCenterIncidenceOutcome`, `pureEdgeStarLeafCycle_centerIncidenceOutcome`, `exists_minimal_pureEdgeStarLeafCycle_centerIncidenceOutcome` | aggregates all center/leaf incidences into an empty/proper/saturated trichotomy.  Empty overlap retains the sharp `2d+1<=m+1` bound.  Proper nonempty overlap displays both an internal incidence and an external center, giving `d+2<=m+1`.  If every center is a leaf, injectivity makes the unique center-to-leaf index map a permutation; it has no fixed points, its image leaf never equals the source's original successor, and every exact affine recurrence remains attached.  Next identify the original cycle successor as an index permutation and compare its components with the center permutation; summing or iterating the resulting recurrence is the direct route to torsion or deletion. |
| `G1PrivateHeavyTargetPureStarLeafPermutationAlgebra.lean`: `minimalFixedPointFreeCycle_exists_successorIndexPerm`, `sum_eq_card_nsmul_of_two_zsmul_perm_eq_const_add_perm`, `PureEdgeStarLeafPermutationAlgebra`, `pureEdgeStarLeafCycle_saturatedPermutationAlgebra`, `exists_minimal_pureEdgeStarLeafCycle_permutationOutcome` | identifies the original least-period successor with a second index permutation `S`.  In the saturated branch the exact equations become `2g(leaf(Pj))=h+g(star)+g(leaf(Sj))`, where the center permutation satisfies `Pj!=j` and `Pj!=Sj`.  Summing over all indices cancels both permutations and gives the new cycle-wide group identity `Σ_j g(leaf_j)=d•(h+g(star))`.  The global endpoint leaves every nonsaturated pattern in one of the two explicit capacity arms and equips the only remaining branch with this full pointwise and summed permutation algebra.  Next conjugate by `P` or `S` and analyze the components of their relative permutation; iterating the affine recurrence around such a component gives the prospective odd torsion relation. |
| `G1PrivateHeavyTargetPureStarLeafRelativeTorsion.lean`: `apply_iterate_eq_pow_two_nsmul_of_apply_eq_two_nsmul`, `pow_two_sub_one_nsmul_eq_zero_of_iterate_eq`, `perm_symm_trans_fixedPointFree_of_apply_ne`, `exists_relativePermCycle_oddTorsion`, `PureEdgeStarLeafPermutationAlgebra.relativeTorsion`, `exists_minimal_pureEdgeStarLeafCycle_relativeTorsionOutcome` | conjugates the saturated recurrence by `P` and forms the fixed-point-free relative permutation `R=P.symm.trans S`.  For `x_i=g(leaf_i)` and `c=h+g(star)`, the shifted values obey `x_(Ri)-c=2(x_i-c)`.  A finite `R`-component has some length `2<=ell<=d`; iteration now proves the exact odd-torsion relation `(2^ell-1)•(g(leaf_i)-(h+g(star)))=0`, with oddness of the Mersenne annihilator proved in Lean.  Thus the global noncrossing star endpoint is reduced to the two coordinate-capacity arms or one explicit bounded odd-torsion obstruction.  Next exploit cyclic modulus arithmetic and validity to show that this torsion element either vanishes in a rigid way yielding deletion, or forces enough odd primary order to contradict the critical range. |
| `G1PrivateHeavyTargetPureStarLeafTorsionFactor.lean`: `PureEdgeStarLeafRelativeTorsionAlgebra.commonTouched_or_notCoprimeCard`, `PureEdgeStarLeafRelativeTorsionAlgebra.commonTouched_or_notCoprimeOddFactor`, `PureEdgeStarLeafTorsionFactorOutcome`, `pureEdgeStarLeafCycle_torsionFactorOutcome_of_relativeTorsionOutcome`, `exists_minimal_pureEdgeStarLeafCycle_torsionFactorOutcome` | performs the exact arithmetic split.  In any finite group, if `2^ell-1` is coprime to the group order then its nsmul map is injective, so the shifted leaf value vanishes; this gives `g(leaf)-g(star)=h`, and the established pair-difference theorem yields common touch/deletion.  For `ZMod(2^t q)`, oddness makes the annihilator automatically coprime to `2^t`; hence the no-common-touch branch can survive only if `gcd(2^ell-1,q)>1` for some `2<=ell<=d`.  The global cyclic endpoint is now capacity or a bounded Mersenne divisor of the odd modulus factor.  Next combine the critical upper bound on `q`, the bound `ell<=d`, and the retained transversal/quarter data to exclude or recursively charge these shared-factor cases. |
| `G1PrivateHeavyTargetPureStarLeafPrimeFactor.lean`: `MersennePrimeOrderCertificate`, `exists_mersennePrimeOrderCertificate_of_notCoprime`, `PureEdgeStarLeafPrimeFactorOutcome`, `pureEdgeStarLeafCycle_primeFactorOutcome_of_torsionFactorOutcome`, `exists_minimal_pureEdgeStarLeafCycle_primeFactorOutcome` | resolves the nontrivial gcd into an explicit odd prime `p` dividing both `q` and `2^ell-1`.  Its order-of-two certificate has `2<=ord_p(2)<=ell<=d`, `ord_p(2)|ell`, and `ord_p(2)|(p-1)`, while also recording `p<=q` and `p<=2^ell-1`.  The original torsion equation and full relative-permutation algebra remain attached.  Thus the sole non-capacity pure-star survivor is now a bounded-order odd-primary obstruction rather than an opaque gcd.  Next use the critical upper bound and the retained transversal/quarter geometry to rule out or recursively charge this prime/order stratum. |
| `G1PrivateHeavyTargetPureStarLeafOddPrimary.lean`: `MersenneTorsionPrimeCertificate`, `exists_mersenneTorsionPrimeCertificate`, `PureEdgeStarLeafOddPrimaryOutcome`, `pureEdgeStarLeafCycle_oddPrimaryOutcome_of_primeFactorOutcome`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryOutcome` | ties the arithmetic factor to the actual leaf displacement `y=g(leaf)-(h+g(star))`.  Under no common touch, `y!=0`; hence its additive order `r` satisfies `2<=r`, is odd, and divides both `q` and `2^ell-1`.  The selected prime `p` now divides this actual subgroup order, not merely the numerical gcd, and still has `2<=ord_p(2)<=ell<=d`.  This identifies the concrete nonzero cyclic subgroup `zmultiples y` available for an odd-primary quotient/descent while retaining every preceding capacity and permutation alternative.  Next formulate the quotient-validity/transversal condition for this subgroup and charge the resulting dimension loss against the critical range. |
| `G1OddPrimaryWitnessTransversal.lean`: `zeroWitness_quotient_zmultiples_iff_exists_nonzero_zsmulWitness`, `embedded_zeroWitness_quotient_zmultiples_iff`, `validTuple_quotient_zmultiples_iff_no_supported_nonzeroWitness`, `CyclicKernelWitnessTransversal`, `quotient_valid_of_cyclicKernelWitnessTransversal`, `quotZModZMultiplesEquivZModDivOrder`, `MersenneTorsionPrimeCertificate.admitsValidTuple_oddFactorQuotient` | gives the exact general quotient kernel for an arbitrary cyclic subgroup: downstairs zero witnesses are precisely original witnesses at nonzero multiples of the generator.  It characterizes retained-subtuple validity by absence of supported such witnesses and turns any deleted-coordinate transversal into a valid quotient tuple.  For the pure-star element `y`, the quotient is explicitly `ZMod (2^t*(q/addOrderOf y))`; the two-adic factor is unchanged and the odd factor decreases strictly.  Thus the remaining task is now combinatorial and dimension-sensitive: find a sufficiently small transversal for all nonzero `zmultiples y` witness layers using the retained leaf/center/quarter geometry, then compare that coordinate loss with the critical endpoint. |
| `G1OddPrimaryMinimalTransversal.lean`: `CyclicKernelSupportTransversal`, `MinimalCyclicKernelSupportTransversal`, `exists_minimalCyclicKernelSupportTransversal_subset`, `exists_private_witness_of_minimalCyclicKernelTransversal`, `minimalCyclicKernelPrivateWitness_coeff_injective`, `exists_minimalCyclicKernelTransversal_descent`, `PureEdgeStarLeafOddPrimaryDescentOutcome`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryDescentOutcome` | shrinks the full-coordinate cyclic-kernel transversal to an inclusion-minimal deletion set `B`.  Each `b∈B` owns a selected witness at a nonzero multiple of `y`, nonzero at `b` and zero at every other point of `B`; the selected coefficient vectors are injective in `b`.  Deleting `B` gives a valid `(m-B.card)`-tuple at the strict odd-factor quotient `2^t*(q/addOrderOf y)`.  This entire package is installed in the global pure-star endpoint without losing its cycle, permutation, torsion, prime-order, or capacity data.  Next derive a quantitative bound on `B.card` from the private kernel-witness family and check the exact critical stratum inequality that pays for this dimension loss. |
| `G1OddPrimaryCriticalCharge.lean`: `OddPrimaryStratumCharge`, `OddPrimaryRecursiveCounterexample`, `OddPrimaryRecursiveCounterexample.two_le_dimension`, `stratumBound_le_of_oddFactorQuotient_lowerBound`, `oddFactorQuotient_lt_stratumBound_of_critical`, `oddPrimaryStratumCharge_zero`, `oddPrimaryRecursiveCounterexample_or_chargeFailure`, `OddPrimaryMinimalTransversalCriticalDescent`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryCriticalChargeOutcome` | isolates the exact inequality `stratumBound n t ≤ r*stratumBound (n-b) t` that pays for quotienting by an order-`r` subgroup while deleting `b` coordinates.  If it holds, every critical tuple descends to a valid tuple below the lower-dimensional endpoint and with strictly smaller odd factor; positivity forces the descended dimension to remain at least two, so it is genuinely induction-ready.  If `b=0`, the charge holds automatically.  The global pure-star endpoint now leaves only a recursive critical instance or a nonempty minimal transversal for which this exact charge fails, while retaining the quotient tuple and all private witnesses in both arms.  Next use the private witness/cycle geometry to prove the charge, or derive a sharp numerical upper bound on `B.card` sufficient for it. |
| `G1OddPrimaryDyadicCharge.lean`: `two_pow_pred_le_stratumBound`, `oddPrimaryStratumCharge_of_two_pow_card`, `order_lt_two_pow_succ_of_oddPrimaryStratumChargeFailure`, `log_order_le_card_of_oddPrimaryStratumChargeFailure`, `OddPrimaryDyadicChargeFailureRegime`, `OddPrimaryMinimalTransversalDyadicDescent`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryDyadicChargeOutcome` | proves the uniform half-cube floor `2^(k-1)≤stratumBound k t` for `k≥2`, hence the concrete sufficient charge `2^(b+1)≤r` for an order-`r` quotient deleting `b` coordinates.  Every failed charge is now localized further: either fewer than two coordinates remain, or `r<2^(b+1)` and `floor(log_2 r)≤b`.  This numerical split is attached losslessly to the global pure-star endpoint.  Next use the private witness and cycle/center/quarter data to exclude near-total deletion and to contradict the logarithmic lower bound on `B.card`, or replace the half-cube estimate by a sharper stratum-specific charge. |
| `G1OddPrimarySingletonComplement.lean`: `private_kernelWitness_pair_difference_mem_zmultiples`, `validTuple_sub_const`, `card_lt_of_nonempty_minimalCyclicKernelSupportTransversal`, `exists_singletonComplement_all_differences_mem_zmultiples`, `two_pow_pred_le_addOrderOf_of_nearTotal_minimalTransversal`, `not_nearTotal_minimalCyclicKernelTransversal_of_critical_evenStratum`, `OddPrimaryLogChargeFailureRegime`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryLogChargeOutcome` | eliminates the near-total deletion arm.  Minimality forbids deleting every coordinate.  If only one coordinate remains, each private witness has two-point support and forces its owner difference into `zmultiples y`; translating at the retained point puts the full valid tuple inside that order-`r` subgroup.  The general abelian bound gives `2^(n-1)≤r≤q`, contradicting criticality whenever `t≥1`.  Thus the sole nonrecursive pure-star survivor retains at least two coordinates and satisfies the exact charge failure together with `r<2^(b+1)` and `floor(log_2 r)≤b`.  Next obtain a geometric upper bound on the minimal transversal incompatible with this logarithmic lower bound, or sharpen the exact charge using the retained cycle data. |
| `G1OddPrimaryCycleLayer.lean`: `validTuple_subsetSum_eq_of_card_eq`, `choose_le_addOrderOf_of_translated_coordinates_mem_zmultiples`, `choose_le_addOrderOf_of_minimal_doublingCycle`, `exists_minimal_relativePermCycle_oddTorsion_layerBounds`, `PureEdgeStarLeafPermutationAlgebra.cycleLayerBounds` | extracts a general exponential lower bound from the saturated relative cycle.  Validity makes equal-cardinality subset sums of distinct tuple coordinates injective.  A least relative component of length `ell` satisfies `y(Rj)=2*y(j)`, so all its translated coordinates lie in `zmultiples y`; consequently `Nat.choose ell k ≤ addOrderOf y` for every layer `k`, while the same `y` is annihilated by `2^ell-1`.  In particular the middle binomial layer lower-bounds the actual odd-primary kernel order, replacing the former prime-factor-only information by a subgroup-scale constraint.  Next thread this least-component certificate into the lossless log-charge endpoint and combine its middle-layer bound with the transversal and ambient cycle-capacity inequalities. |
| `G1OddPrimaryCycleLayerCharge.lean`: `PureEdgeStarLeafRelativeTorsionAlgebra.permutationAlgebra`, `PureEdgeStarLeafOddPrimaryCycleLayerChargeOutcome`, `pureEdgeStarLeafCycle_cycleLayerChargeOutcome_of_logChargeOutcome`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryCycleLayerChargeOutcome` | installs the least relative component losslessly in the global critical endpoint.  The saturated branch reselects one component and rebuilds the Mersenne prime certificate, minimal cyclic-kernel transversal, quotient tuple, and recursive/log-charge split around exactly its initial displacement.  It simultaneously retains the original relative-torsion algebra, `binom(ell,k)≤r` for every layer, `(2^ell-1)•y=0`, `2≤ell≤d`, and all private-witness descent data.  The remaining task is no longer data alignment: combine the middle-binomial lower bound with the failed exact charge, `log_2(r)≤|B|`, and the outer cycle/ambient capacity constraints. |
| `G1OddPrimaryFullCycleSubgroup.lean`: `two_pow_pred_le_card_of_validTuple`, `oddTorsion_mem_oddPrimary_zmultiples`, `PureEdgeStarLeafPermutationAlgebra.allDisplacements_mem_oddPrimary`, `PureEdgeStarLeafPermutationAlgebra.exists_fullCycleOddKernelGenerator`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleSubgroupOutcome` | combines all relative components into one cyclic descent object.  Every leaf displacement is annihilated by an odd Mersenne coefficient obtained from the order of `R=P^{-1}S`, hence belongs to the order-`q` primary subgroup of `ZMod (2^t q)`.  The subgroup generated by all `d` displacements is cyclic; restricting and translating the valid tuple into it gives a generator `y_full` with `2^(d-1)≤addOrderOf(y_full)` and `addOrderOf(y_full)∣q`.  The global endpoint retains this full-cycle generator alongside the least-component/log-charge package.  Next construct the minimal-transversal quotient for `y_full`; any failed charge must then have `d-1≤|B_full|`, directly coupling the outer cycle length to deletion cost. |
| `G1OddPrimaryFullCycleCharge.lean`: `not_nearTotal_minimalCyclicKernelTransversal_of_order_le_oddFactor`, `OddPrimaryFullCycleMinimalTransversalChargeDescent`, `exists_fullCycleMinimalTransversalChargeDescent`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleChargeOutcome` | constructs the minimal cyclic-kernel transversal around the full-cycle generator itself.  The quotient is a valid tuple at `2^t*(q/addOrderOf y_full)` with strictly smaller odd factor and retains one private nonzero kernel witness per deleted coordinate.  Exact charge gives a recursive critical tuple.  On charge failure, the certificate-free singleton-complement argument leaves at least two quotient coordinates; since `2^(d-1)≤addOrderOf y_full`, the dyadic sufficient charge forces `d-1≤|B_full|`.  The remaining private-heavy task is to combine this direct cycle/deletion inequality with the retained owner/quarter and private-witness incidence data. |
| `G1OddPrimaryFullCycleIncidence.lean`: `mem_left_or_mem_right_of_pairDifference_mem_zmultiples`, `card_cycleRange_sdiff_cyclicKernelTransversal_le_one`, `pred_le_card_cyclicKernelTransversal_inter_cycleRange`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleIncidenceOutcome` | identifies the structural content of the full-generator transversal.  Every difference of two distinct cycle leaves is a nonzero multiple of `y_full`, and its two-coordinate coefficient vector is a kernel-layer witness.  Therefore `B_full` hits every leaf pair: at most one of the `d` leaves lies outside `B_full`, and `d-1≤|B_full∩leafRange|`.  This all-but-one incidence holds in both recursive and charge-failure arms and localizes the deletion cost directly on the saturated leaf cycle.  Next exploit the private witnesses owned by these deleted leaves together with the center permutation and quarter geometry. |
| `G1OddPrimaryFullCyclePrivateFamily.lean`: `CycleLeafKernelPrivateWitnessFamily`, `card_cycleIndicesInTransversal_eq_card_inter_cycleRange`, `exists_cycleLeafKernelPrivateWitnessFamily`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCyclePrivateFamilyOutcome` | restricts the canonical private-witness choice to the cycle leaves contained in `B_full`.  It produces an index set `J` with `d-1≤|J|` and pairwise distinct nonzero cyclic-kernel witnesses.  On the indexed cycle leaves their coefficient matrix is diagonal: each row is nonzero at its owner and zero at every other member of `J`.  This is a general, losslessly retained counting object in both charge arms.  Next transfer its vanishing pattern through the saturated center permutation, where every row can meet at most its owner center and the single undeleted leaf center. |
| `G1OddPrimaryFullCycleCenterSparse.lean`: `CycleCenterSparseKernelPrivateWitnessFamily`, `exists_cycleCenterSparseKernelPrivateWitnessFamily`, `pureEdgeStarLeafCycle_centerSparseOutcome_of_cycleLayerChargeOutcome`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleCenterSparseOutcome` | transfers the large private family through the saturated center permutation `center(k)=leaf(P k)`.  At most one center lies outside `B_full`.  For every one of at least `d-1` leaf-owned rows, the owner-center coefficient is nonzero, all nonzero center positions lie either at that owner or at the possible unique undeleted center, and the center-support cardinality is at most two.  The endpoint rebuilds and retains the full-generator quotient/charge/incidence data directly from the aligned cycle-layer branch.  Next combine these sparse rows with their zero-sum and affine cycle equations to control support outside the center/leaf range. |
| `G1OddPrimaryFullCycleSparseRow.lean`: `ExactSignedPairWitness`, `externalSupport_or_exactSignedCenterPair`, `CycleCenterSparseExternalOrCommonPivot`, `cycleCenterSparse_external_or_commonPivot`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleSparseRowOutcome` | resolves the zero-sum algebra of every center-sparse private row.  A row either has a nonzero coefficient outside the common center/leaf range or is exactly a signed pair between its owner-center and a center outside `B_full`.  Since at most one such center exists, the full family has a sharp normal form: either every row has external support, or all internally supported rows use one common undeleted pivot.  The normal form now explicitly preserves center injectivity, membership of every owner-center in `B_full`, and the nonzero owner diagonal, as well as the same coefficient rows and quotient/charge data. |
| `G1OddPrimaryFullCyclePivotStar.lean`: `CycleCenterSparseExternalOrFullPivotStar`, `cycleCenterSparse_external_or_fullPivotStar`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCyclePivotStarOutcome` | sharpens the family normal form using `d≥2`, hence nonempty owner set `J`.  Either at least one selected row has a nonzero coordinate outside the center/leaf range, or no row does and every one of the at least `d-1` rows is an exact signed pair to one common center outside `B_full`.  This removes the former mixed wording and isolates two disjoint structural branches.  Next use the relative doubling recurrence to show that the full pivot-star differences generate the complete odd-primary leaf subgroup; route the external row into the retained ambient-capacity machinery. |
| `G1OddPrimaryFullCyclePivotGeneration.lean`: `PureEdgeStarLeafPermutationAlgebra.exists_fullCycleOddKernelGenerator_with_span`, `closure_signedPivotTargets_eq_zmultiples_of_doubling`, `cycleCenterSparse_external_or_generatingPivotStar`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCyclePivotGenerationOutcome` | retains the exact equality between the subgroup generated by all translated cycle leaves and `zmultiples y_full`.  Abstractly, if two permutations satisfy the relative doubling recurrence and signed differences from every non-pivot leaf to one pivot are selected, those targets generate the entire leaf subgroup: modulo their closure every leaf displacement is equal, while the recurrence forces that common class to equal twice itself.  Consequently the internal branch is now a genuinely generating pivot star; otherwise an external private-row incidence survives.  Next extract arithmetic consequences from the generating scalar family and route the external branch through retained ambient capacity. |
| `G1OddPrimaryFullCyclePivotArithmetic.lean`: `GeneratingScalarArithmetic`, `generatingScalarArithmetic_of_closure_eq_zmultiples`, `cycleCenterSparse_external_or_arithmeticPivotStar`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCyclePivotArithmeticOutcome` | turns subgroup generation into a concrete finite integer certificate.  There are weights `w_j` such that `addOrderOf(y_full)` divides `sum_j w_j*scalar_j-1`; consequently, for every prime dividing the kernel order, at least one selected private-row scalar is not divisible by that prime.  The global endpoint retains this Bezout/prime-coverage arithmetic in the full pivot-star arm and preserves the explicit external-row alternative.  Next combine prime coverage with coefficient and owner/quarter restrictions, while routing the external row through retained ambient capacity. |
| `G1OddPrimaryFullCycleRetainedExternal.lean`: `OddPrimaryFullCycleMinimalTransversalChargeDescent.two_le_retained`, `exists_not_mem_of_two_le_complement_and_sdiff_le_one`, `OddPrimaryFullCycleIncidenceChargeDescent.exists_retained_outside_cycleRange`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleRetainedExternalOutcome` | observes that both the recursive and failed-charge arms retain at least two quotient coordinates.  Since the full-generator transversal leaves at most one cycle leaf undeleted, one retained coordinate necessarily lies outside the saturated leaf range, which equals the center range.  The global endpoint now names this external quotient coordinate while retaining the pivot arithmetic and explicit external-row split.  Next relate external-row support to this retained ambient set and use the named outside coordinate in owner/quarter capacity. |
| `G1OddPrimaryFullCycleExternalPrivacy.lean`: `HasRetainedExternalCenterSupport`, `hasRetainedExternalCenterSupport_of_private`, `cycleCenterSparse_retainedExternal_or_arithmeticPivotStar`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleExternalPrivacyOutcome` | restores the canonical rows' full minimal-transversal privacy through the sparse, pivot, generation, and arithmetic layers.  A nonzero coefficient outside the center range cannot occur at the row's owner; privacy therefore forces that support coordinate outside `B_full`.  The first branch now names an actually retained external row coordinate, while the second retains the generating pivot star and Bezout/prime-coverage certificate.  Next compare the retained external support and ambient coordinate with the original owner/quarter data, and route the prime-unit internal row separately. |
| `G1OddPrimaryFullCycleRetainedMixed.lean`: `CycleCenterSparseRetainedExternalOrCommonPivot`, `cycleCenterSparse_retainedExternal_or_commonPivot`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleRetainedMixedOutcome` | preserves the classification of every selected row even when the sharp external branch fires.  Either all at least `d-1` rows have retained support outside the center range, or one common center outside `B_full` is a pivot and every row is either retained-external or an exact signed owner/pivot pair.  Center injectivity, deleted owner membership, and the nonzero owner diagonal are retained with the same rows.  This losslessly coexists with the sharp full-pivot generation/Bezout alternative and makes the number of external versus internal rows a usable parameter. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `finiteMap_capacity_or_largeFiber`, `witnessNonzeroCoefficientLevels`, `card_witnessNonzeroCoefficientLevels`, `witness_nonzeroCoefficient_mem_levels`, `FixedExternalCoefficientPrivateFiber`, `nonzeroZMultiples`, `card_nonzeroZMultiples`, `fixedExternalCoefficientPrivateFiber_card_le_order_sub_one_or_pairGaps`, `fixedExternalCoefficientPrivateFiber_equalTarget_pair_heavyDiagonal_or_externalGaps`, `fixedExternalFiberHeavyDiagonalRows`, `fixedExternalFiberLightDiagonalRows`, `card_fixedExternalFiberHeavy_add_light`, `card_univ_sdiff_erase_of_not_mem`, `fixedExternalCoefficientPrivateFiber_repeatedTarget_lightGapFrontier`, `fixedExternalFiberPositiveRowsAt`, `fixedExternalFiberDirectedGapPairsAt`, `card_fixedExternalFiberDirectedGapPairsAt_le`, `card_selectedFixedExternalGapFiber_le_light_mul_positiveRows`, `fixedExternalCoefficientPrivateFiber_heavyDiagonal_twoRetained_shape`, `RetainedExternalInternalRowPartition`, `retainedExternalInternalRowPartition_of_mixed`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleRowPartitionOutcome` | turns the mixed normal form into explicit disjoint finite row sets `E` and `I` with `E∪I=J` and `d-1≤|E|+|I|`.  Every external row receives a chosen nonzero coordinate in the retained ambient set `R=(univ\B_full)\centerRange`; either `I` is empty or every internal row is an exact signed pair to one common undeleted pivot.  Nonzero witness coefficients lie in the exact `n+1`-element alphabet `{-1}∪[1,n]`.  Thus, for every threshold `K`, the endpoint proves both `|E|≤|R|K` or a coordinate used by more than `K` rows, and `|E|≤|R|(n+1)K` or a fixed `(coordinate, coefficient)` fiber above `K`.  In the latter fiber, owner columns are distinct deleted coordinates, complete rows remain distinct, every owner diagonal is nonzero, every off-diagonal owner entry is zero, and the shared external column equals one fixed nonzero integer.  A fixed fiber either has at most `addOrderOf(y)-1` rows or two distinct rows share a target; validity then forces mutually directed gaps at distinct coordinates away from the common external column, each at the gaining owner or outside `B_full`.  For an equal-target pair, either one private owner diagonal is at least two or both directed gaps are genuinely retained-external, distinct, and away from the common column.  For any repeated-target subfamily, its light-diagonal rows `L` now contribute exactly `|L|(|L|-1)` ordered pairs, each assigned an external directed gap away from the common column.  Adaptively, either `|L|(|L|-1)≤(n-|B_full|-1)K` or one retained coordinate supports more than `K` chosen gaps.  At a fixed gap coordinate `w`, every edge targets a row positive at `w`, yielding `#GapPairs(w)≤|L|·#PositiveRows(w)` both for the full directed-gap relation and the selected adaptive fiber.  If at most two coordinates survive deletion, every owner-heavy row is moreover forced to have common coefficient `-1`, diagonal coefficient `2`, exact omissions `{x,z}`, and coefficient vector `pureEdgeCoeffs(owner,x,z)`.  Next compare these rigid heavy pure edges and charge high-multiplicity positive-row incidence to crossing/deletion structure. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `sameCycle_doubling_eq_pow_two_nsmul`, `sameCycle_affineTargets_sub_eq_mersenne_nsmul` | supplies the generic relative-component comparison used by the new affine row endpoint.  In one component of a doubling permutation, two owner displacements differ by a power-of-two iterate; if their rows share slope `epsilon` and offset, their target difference is exactly `epsilon • ((2^k-1) • displacement)`.  Thus same-component row collisions are converted into the odd Mersenne divisibility language already carried by the odd-primary certificate. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `fixedExternalCoefficientPrivateFiber_equalTarget_twoHeavy_twoRetained_commonTouched` | closes the equal-target owner-heavy pair when at most two coordinates survive deletion.  The two row-shape theorems force the same exact omission pair and coefficient `2` at distinct private owners.  Subtracting their equal target equations gives equality of the doubled owner values; validity and uniqueness of the nonzero involution then produce a coordinate touched by every half-witness, i.e. the G1 one-coordinate deletion conclusion.  The remaining two-retained repeated-target obstruction can therefore contain at most one owner-heavy row; its light/positive-row incidence still requires a separate charge. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `fixedExternalCoefficientPrivateFiber_equalTarget_twoLight_twoRetained_false` | eliminates the opposite equal-target extreme in the same sharp regime.  Two distinct light rows would force two distinct directed gaps outside `B_full`, both away from the fixed external column `x`; together with `x` these are three distinct retained coordinates, contradicting `n-|B_full|≤2`.  Thus a no-common-touch repeated-target fiber with two retained coordinates has at most one heavy and at most one light row. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `fixedExternalCoefficientPrivateFiber_equalTarget_heavyLight_twoRetained_shapes` | classifies the sole remaining two-retained target collision.  If `f` is owner-heavy and `k` is light, the heavy row fixes the retained pair `{x,z}` and `lambda=-1`.  The reverse validity gap must occur at `z`; privacy and the zero-sum identity then force `k(owner_k)=-1` and `k(z)=2`.  Thus the two rows are exactly the adjacent pure edges `pureEdgeCoeffs(owner_f,x,z)` and `pureEdgeCoeffs(z,x,owner_k)`.  This routes the mixed collision into the established center-changing pure-edge transition algebra. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `fixedExternalCoefficientPrivateFiber_sameTarget_card_le_two_of_noCommonTouched`, `fixedExternalCoefficientPrivateFiber_card_le_two_mul_order_sub_one_of_twoRetained` | aggregates the two-retained classification.  Under no common touch, every same-target subfamily partitions into at most one heavy and at most one light row, hence has cardinality at most two.  Mapping the entire fixed coefficient fiber into the punctured cyclic target subgroup then gives `|F|≤2(addOrderOf(y)-1)`.  This is the sharp target-multiplicity consequence of the small-complement structure; every size-two fiber is the adjacent pure-edge transition above. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `fixedExternalCoefficientPrivateFiber_twoRetained_rowProfile`, `twoRetainedExternalCoefficientLevels`, `card_twoRetainedExternalCoefficientLevels`, `fixedExternalCoefficientPrivateFiber_lambda_mem_twoRetainedLevels` | classifies every row, not only collisions, when the retained complement has cardinality exactly two.  Privacy restricts support to the private owner and the retained pair `{x,z}`; zero coefficient sum leaves precisely five profiles.  The common external coefficient is therefore in the exact constant-size alphabet `{-1,1,2}` (cardinality three), replacing the generic `n+1` coefficient levels in this sharp branch. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `twoRetainedExternalCoefficientLevel_isUnit_mod_odd`, `fixedExternalCoefficientPrivateFiber_lambda_isUnit_mod_odd` | proves that every coefficient in the exact alphabet `{-1,1,2}` is invertible modulo every odd modulus.  In particular, reduction to any odd-prime layer preserves the common external column of a fixed fiber and permits coefficient normalization without losing rows. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `privateWitness_externalCoefficient_mem_twoRetainedLevels`, `twoRetainedExternalRows_capacity_or_largePrivateFiber` | applies the three-level classification before selecting a fiber.  Every private external row maps into `R×{-1,1,2}`, with `|R|≤2`; hence for every threshold `K`, either `|E|≤6K` or one fixed `(coordinate,coefficient)` label supports more than `K` rows.  The large arm retains the full injective private-owner diagonal, distinct coefficient rows, and common external column, so all target and pair-shape theorems apply without rebuilding data. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `TwoRetainedExternalInternalRowFrontier`, `twoRetainedExternalInternalRowFrontier_of_rowPartition` | reintegrates the constant-six estimate without reselecting data.  From the existing row-partition endpoint and `n-|B|=2`, it extracts the same `scalar`, `coeff`, `E`, `I`, and `supportCoord`, retains the exact partition identities, `d-1≤|E|+|I|`, all row witnesses, and the common-pivot exact signed-pair arm, and adds the constant-six large-private-fiber frontier. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `fixedExternalCoefficientPrivateFiber_twoRetained_signedPair_or_pureEdge` | upgrades all five numerical profiles to exact geometry.  Every external row is either an `ExactSignedPairWitness` between its private owner and the common retained coordinate, or a `pureEdgeCoeffs` vector centered at the owner, the common coordinate, or the second retained coordinate.  Thus the external class and the pre-existing internal common-pivot class now share one signed-edge/pure-edge language suitable for cycle comparison. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `witness_target_eq_of_coeff_eq_pureEdgeCoeffs`, `fixedExternalCoefficientPrivateFiber_twoRetained_familyAffineTargets` | converts the signed/pure geometry into the affine equations needed by the relative cycle algebra.  The second retained coordinate is selected once for the whole fiber, and every target is one of three fixed affine functions of its private owner, with the owner coefficient retained in the profile.  The `lambda=1` and `lambda=2` classes already have a unique law; only `lambda=-1` retains three possible owner slopes. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `fixedExternalCoefficientPrivateFiber_ownerCoefficient_mem_twoRetainedLevels`, `fixedExternalCoefficientPrivateFiber_twoRetained_capacity_or_largeAffineProfile` | proves that the private-owner coefficient also lies in `{-1,1,2}` and performs adaptive profile extraction.  For every `K`, either the fixed external fiber has at most `3K` rows or more than `K` rows share one owner coefficient and therefore one of the five exact affine target laws.  This leaves only a constant factor-three profile loss before comparison with relative-permutation components. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `FixedExternalTwoRetainedAffineProfileAbove`, `fixedExternalCoefficientPrivateFiber_twoRetained_affineProfileAbove_of_largeFiber`, `twoRetainedExternalInternalRowFrontier_largeInternal_or_largeAffineExternal` | composes the factor-three profile extraction with the external/internal frontier at its natural scale.  The final lossless endpoint gives either `d-1≤2|I|` for a common-pivot signed-pair class or an external subfamily of more than `(d-1)/36` rows satisfying one fixed affine owner law.  The partition, witnesses, fixed external fiber, common retained coordinates, and exact affine equation all remain available for componentwise cycle analysis. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `FixedExternalTwoRetainedRelativeAffineProfileAbove`, `FixedExternalTwoRetainedAffineProfileAbove.relative` | rewrites each of the five dense external laws relative to an arbitrary leaf base.  The selected rows then share one equation `target=epsilon•(ownerDisplacement)+offset`, with a global slope `epsilon∈{-1,1,2}` and global offset.  Together with the odd-modulus unit theorem and the same-cycle Mersenne comparison, this places the external branch in the same translated odd-primary language as the internal pivot branch. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `permutationFamilyComponents`, `permutationFamily_large_affineComponentFrontier`, `FixedExternalTwoRetainedRelativeAffineProfileAbove.cycleComponentFrontier` | partitions an arbitrary finite affine family by the components of a doubling permutation and counts only components actually occupied.  A family above threshold `L` either has occupied-component budget greater than `L`, or more than `K` rows lie in one component; every pair in that component has target difference `epsilon•((2^k-1)•ownerDisplacement)`.  The specialization preserves the dense selected external rows, their common slope and offset, and their exact coefficient profile. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `permutationSubsetFullComponents`, `permutationSubsetBoundary`, `card_permutationFamilyComponents_le_full_add_boundary`, `permutationFamily_affine_fullComponent_or_boundary_or_largeComponent` | splits occupied components into components fully covered by selected owners and components with a selected owner whose successor is unselected.  Selection propagates around a finite cycle when no such boundary exists, giving the quantitative charge `occupied≤full+boundary`.  The adaptive affine theorem therefore forces excess full components, excess mixed-transition boundaries, or a large component with pairwise Mersenne target comparisons; the dense external payload retains both the original occupied-component bound and this stronger charge. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `permutationFamilyBoundaryRows`, `card_permutationFamilyBoundaryRows_eq_boundary`, `permutationFamilyBoundary_uniqueRow`, `permutationFamilyFullComponent_uniqueSuccessorRow_affine`, `fixedExternalSelectedOwner_injective` | lifts the owner-component split back to actual selected rows without multiplicity loss.  An injective family has exactly one boundary source row per boundary owner.  Inside a full component every selected row has a unique selected successor row in the same component, and an affine doubling family satisfies the exact centered recurrence `target(successor)-offset=2(target(row)-offset)`.  The nested fixed-external row owner map is structurally injective, and that fact is retained by the dense component-frontier payload, so both lifts apply directly to the global exact-two external branch. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `nestedSelectedBoundaryRow_successor_firstFailure_of_boundary`, `nestedFilteredBoundaryRow_successor_transition`, `fixedExternalBoundaryRow_successor_transition` | resolves every boundary row by the first nested selection layer crossed by its relative successor.  The reusable theorem handles an arbitrary outer set, binary partition, fixed-label fiber, and final profile fiber.  In the exact-two external specialization the exhaustive exits are: outside `J`; into the internal class `I`; to a different external `(support coordinate, coefficient)` label; or to the same fixed external fiber with a different private-owner coefficient.  Thus every mixed boundary now carries a concrete transition label drawn from the already bounded alphabets, with no row or cardinality loss. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `nestedBoundaryTransitionTargets`, `card_nestedBoundaryTransitionTargets_le`, `card_nestedSelectedBoundaryRows_le_transitionLayers`, `nestedBoundaryTransitionLayerBudget_eq_card_sub` | integrates the four successor exits into one quantitative mixed-transition charge.  Nested ownership followed by the relative permutation injects boundary source rows into the union of the four explicit target layers, proving `#boundaryRows≤#(univ ∖ J)+#I+#(univ ∖ F)+#(univ ∖ S)`.  For the retained disjoint `E/I` partition this budget telescopes exactly to `card α-#S`; the unsimplified form is kept because its four terms route separately to outer-transversal, internal-pivot, external-label, and owner-profile estimates. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `finiteMap_exists_dominantFiber`, `finiteMap_exists_twoStageDominantFibers`, `twoRetainedExternalRows_exists_dominantPrivateFiber`, `fixedExternalCoefficientPrivateFiber_exists_dominantOwnerProfile`, `fixedExternalCoefficientPrivateFiber_twoRetained_dominantRelativeProfile`, `card_nestedSelectedBoundaryRows_le_outer_add_internal_add_seventeen` | upgrades both finite-alphabet selections from threshold pigeonholes to genuinely dominant fibers.  The exact-two external family now admits a realized label fiber `F` with `#E≤6#F` and full private matrix geometry; inside it, a realized owner profile `S` satisfies `#F≤3#S` and retains one translated affine law with unit slope.  Hence the two inner transition complements cost at most `17#S`, giving `#boundaryRows≤#(univ∖J)+#I+17#S`.  The dominant affine family is now ready to replace the threshold-selected family in the cycle-component endpoint. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `FixedExternalTwoRetainedDominantRelativeAffineCycleComponentFrontier`, `FixedExternalTwoRetainedDominantRelativeAffineProfile.cycleComponentFrontier`, `TwoRetainedExternalInternalDominantCycleComponentFrontier`, `retainedExternalInternalRowPartition_largeInternal_or_dominantCycleComponentExternal`, `PureEdgeStarLeafOddPrimaryFullCycleComponentRowOutcome` | reinserts the globally dominant affine family into the global critical endpoint.  The exact-two external branch now carries the same `S` with `#E≤6#F`, `#F≤3#S`, the constant-17 boundary charge, the unique centered doubling successor on every full selected component, and the occupied-component capacity/Mersenne alternative.  Thus none of the density is reselected or lost between finite-label aggregation and cycle decomposition; only the outer-row and internal-pivot budgets remain to be routed. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `card_fin_compl_le_one_of_sub_one_le_card`, `twoStageDominance_internalSparse_bounds`, `card_nestedSelectedBoundaryRows_le_thirty_five_mul`, `TwoRetainedExternalInternalDominantCycleComponentFrontier` | routes the last two mixed-transition budgets in the globally selected exact-two branch.  From `d-1≤#J`, the outer defect has size at most one.  The external alternative now explicitly retains `2#I<d-1`; combined with `d-1≤#E+#I`, `#E≤6#F`, and `#F≤3#S`, this proves `#I<18#S` and `d-1<36#S`.  Hence the same dominant affine family satisfies the fully routed estimate `#boundaryRows≤35#S`, while the sharper four-layer and constant-17 decompositions remain available. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `fixedExternalFiberPositiveRowsAt_card_le_one_of_mem_deleted`, `fixedExternalFiberPositiveRowsAt_large_eq_fixed_or_companion`, `FixedExternalTwoRetainedDominantRelativeAffineCycleComponentFrontier` | localizes high positive-row incidence in the exact-two global branch.  At a deleted coordinate, privacy makes every positive row use that coordinate as its private owner, so owner injectivity bounds the positive-row set by one.  Consequently any coordinate positive in two selected rows must be one of the fixed external column `x` and the unique companion retained column `z`.  This statement is stored on the same dominant cycle payload for every coordinate; converting the two surviving uniform-column possibilities to canonical crossing or closed-cycle structure remains open. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `fixedExternalFiberPositiveRowsAt_eq_self_or_empty_of_constant`, `fixedExternalCoefficientPrivateFiber_twoRetained_companionCoefficient`, `twoRetainedExternalCoefficientLevels_positive_cases`, `FixedExternalTwoRetainedDominantRelativeAffineCycleComponentFrontier` | resolves the two surviving high-positive columns into exact uniform profiles.  On the selected owner-coefficient fiber `S`, every row has coefficient `lambda` at `x` and `-(mu+lambda)` at `z`; therefore each positive-row set is exactly `S` or empty.  For `lambda,mu∈{-1,1,2}`, positivity at `x` is equivalent to `lambda=1` or `2`, while positivity at `z` is equivalent to `mu=lambda=-1`.  These coefficient and finset equalities are retained in the global cycle payload, leaving a finite signed/pure-edge conversion rather than an incidence-counting problem. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `fixedExternalCoefficientPrivateFiber_twoRetained_selectedRowGeometry`, `FixedExternalTwoRetainedSelectedGeometry`, `fixedExternalCoefficientPrivateFiber_twoRetained_selectedGeometry`, `FixedExternalTwoRetainedDominantRelativeAffineCycleComponentFrontier` | performs that finite conversion without reselecting rows.  Once the dominant owner coefficient `mu` and the global retained companion `z` are fixed, every row of `S` lies in one of exactly five labelled classes: the two signed owner--`x` orientations or one of three fully identified pure-edge vectors.  The same `lambda`, `mu`, `x`, and `z` occur in every row, and this exact family geometry is now stored beside the affine recurrence and boundary charge in the global cycle payload.  The next step is to combine these five cases with quotient-kernel provenance and full-component recurrence; canonical half-collision crossing is not available from coefficient geometry alone. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `FixedExternalTwoRetainedUniformGeometry`, `FixedExternalTwoRetainedSelectedGeometry.uniform`, `FixedExternalTwoRetainedRelativeAffineParameters`, `FixedExternalTwoRetainedRelativeAffineParameters.slope_eq`, `FixedExternalTwoRetainedDominantRelativeAffineCycleComponentFrontier` | collapses the rowwise five-way disjunction to one case for the entire nonempty selected family.  It also retains the exact translation offset in each case and proves that the homogeneous affine slope is always the selected private-owner coefficient `mu`.  Accordingly, the dominant cycle payload now states both its affine law and every componentwise Mersenne comparison directly with `mu`, aligning the cycle recurrence with the actual quotient-kernel coefficient rather than an independently named unit. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `affineOffset_mem_zmultiples`, `FixedExternalTwoRetainedDominantRelativeAffineCycleComponentFrontier`, `retainedExternalInternalRowPartition_largeInternal_or_dominantCycleComponentExternal`, `PureEdgeStarLeafOddPrimaryFullCycleComponentRowOutcome` | connects the owner-aligned profile to the full cyclic-kernel generator.  At the global endpoint every owner displacement and every row target lies in `ℤ·y`, so the exact affine law forces one integer `rho` with `rho·y=offset`.  On every full selected component the unique successor now carries both the centered target recurrence and its scalar form `(scalar(next)-rho)·y = 2·((scalar(row)-rho)·y)`.  Thus the remaining closed-cycle task is an arithmetic analysis of centered integers modulo `addOrderOf(y)`, not a reconstruction of canonical collisions. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `alignedCenterSuccessor_relativeDoubling`, `PureEdgeStarLeafOddPrimaryFullCycleAlignedRowPartitionOutcome`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleAlignedRowPartitionOutcome` | reopens the cycle-layer algebra and aligns its successor permutation `S` with the same center permutation `P` carried by the row family.  Injectivity of the minimal leaf cycle makes that `P` unique.  The strengthened global endpoint therefore retains `R=P⁻¹S` and the exact recurrence `disp(Rj)=2•disp(j)` alongside the rows; nested earlier capacity branches are propagated outward. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `TwoRetainedExternalInternalCycleComponentFrontier`, `twoRetainedExternalInternalRowFrontier_largeInternal_or_cycleComponentExternal`, `PureEdgeStarLeafOddPrimaryFullCycleComponentRowOutcome`, `exists_minimal_pureEdgeStarLeafCycle_oddPrimaryFullCycleComponentRowOutcome` | composes the exact-two row dichotomy through affine normalization and occupied relative-cycle decomposition, then installs it in the global critical endpoint.  The retained quotient now splits explicitly into dimension greater than two, or dimension exactly two; in the latter case Lean returns either a linear-density common-pivot signed-pair family or the full occupied-component/Mersenne external frontier.  All cycle-layer, transversal, sparse-row, and aligned `P,S` data remain available. |
| `G1OddPrimaryFullCycleRowPartition.lean`: `twoRetainedExternalInternalRowFrontier_largeInternal_or_largeExternal` | resolves the constant-six frontier at the scale required by the cycle.  Either the common-pivot internal class satisfies `d-1≤2|I|`, or one fixed external coordinate/coefficient fiber has more than `(d-1)/12` rows.  The theorem retains the exact partition, every witness, the internal signed-pair arm, and the external private-fiber structure, so neither branch loses the geometry needed downstream. |
| `G1ProfileLocalHeavyFrontier.lean`: `WitnessAvoidanceNonProfileResidual`, `criticalGenuineHeavyTwoStepEscape_localHeavyProfileFrontier` | performs the corrected upstream composition without any global-lightness premise.  For `n≥7`, the genuine-heavy two-step escape yields only critical large crossing, an admitted valid `n`-tuple at half modulus, an avoidance/escape-enriched private-heavy protected descent whose minimal transversal now has the sharp small-cardinality/all-but-one-heavy split, two-stage heavy/escape incidence frontier, counted joint-fiber coefficient-gap expansion and its closures, owner/escape normalization (with only the anchor exceptional), explicit joint, fixed external-heavy, and total tail-heavy bounds, a terminal self-heavy common-touch/capacity theorem, and an exact-two omission star whose owner count is charged to one avoiding witness's negative mass, as well as the cycle and omission counts, or the unchanged non-profile frontier.  The pure-edge residual has been eliminated from both exact profiles. |
| `G1CriticalLocalHeavyFrontier.lean`: `critical_localHeavyProfileFrontier` | lifts the corrected genuine-heavy theorem through the enclosing critical-range trichotomy.  Common touch is converted immediately to its one-coordinate half deletion.  Hence every strict critical instance with `n≥7` has four explicit outcomes: critical large crossing, an admitted valid `n`-tuple at half modulus, an avoidance/escape-enriched private-heavy descent with an internal shift, or the independent non-profile avoidance residual. |
| `G1CriticalResidualDeleteSteps.lean`: `CriticalRangeDeleteStepFromSeven`, `CriticalRangeDeleteStepBelowSeven`, `CriticalPrivateHeavyAvoidanceEscapeDeleteStepFromSeven`, `CriticalNonProfileResidualDeleteStepFromSeven`, `criticalRangeDeleteStepFromSeven_of_localHeavyResiduals`, `criticalRangeDeleteStep_of_belowSeven_and_fromSeven`, `global_lower_bound_of_localHeavyResidualDeleteSteps` | states the exact remaining deletion obligations at the corrected G1 boundary.  Large-crossing deletion plus the avoidance/escape-enriched private-heavy and non-profile structural deletion steps implies the critical delete step for every `n≥7`; a separate finite-base interface for `n<7` gives the full `CriticalRangeDeleteStep`.  The conditional global theorem consumes the stronger private premise automatically supplied by every exact-profile branch. |
| `critical_crossingMass_or_commonTouched_or_heavy_or_dominantEscape` | packages the current critical frontier: large crossing product mass, common touch, a heavy witness, or one maximum-weight/minimum-support shape whose counted escaping incidences cover its negative tail and satisfy the exact depth normalization and aggregate external-support tax |
| `G1ThreeDescent.lean`: `pair_descent_order_three`, `exists_validTuple_quotient_of_two_adjacent_heavy_opposites` | gives a generic order-three descent: delete two coordinates differing by nonzero 3-torsion and quotient by their difference, producing a valid tuple two coordinates shorter in a group three times smaller; the adjacent-heavy specialization is retained algebraically but is no longer needed for half-target G1 |
| `quotOrderThreeEquivZMod`, `exists_validTuple_third_of_two_adjacent_heavy_opposites` | identifies a cyclic order-three quotient with `ZMod (N/3)`; this remains reusable when a genuine order-three coordinate pair arises outside the now-closed adjacent-heavy half-target profile |
| `UniqueSums.lean`: `valid_gap` | the SI set is valid at every endpoint $`2^n-2^t`$ with $`2^t\le n`$ |
| `OddOrder.lean`: `chain_order_eq`, `chain_quotient_card_bound_of_joint_dissociated` | exact SI-chain order and automatic residual separation for a chain embedded in a dissociated family |
| `codim_one_chain_odd_card_bound` | a chain missing one coordinate already forces the full odd threshold |
| `mersenne_certificate_order_eq`, `mersenne_certificate_card_bound_of_span` | chain-free Mersenne certificate: dissociation supplies the order lower bound, while coordinatewise annihilation and spanning force the exact Mersenne order |
| `RelationCertificate.lean`: `det_zsmul_eq_zero_of_matrixRelations`, `mersenne_card_bound_of_relation_matrix` | adjugate bridge from an integer relation matrix of determinant `±(2^(m+1)-1)` to the full odd threshold; includes the determinant-15 torsion certificate |
| companion `unique` census: `scripts/relation-certificate-census.py` | exact threshold validation: every SHC tuple mod 15 and 31 has a Mersenne determinant certificate; the mod-35 stress test shows the extraction statement must retain its strict-window hypothesis |
| companion `unique` census: `scripts/strict-window-witness-census.py` | all 10,496 dissociated four-coordinate tuples at odd orders 17–29 have a forbidden head-2 relation; every deletion-saturated tuple has a unit coordinate, giving the next normalization target |
| companion `unique` census: `scripts/five-window-witness-census.py` | all 1,692,224 dissociated five-coordinate tuples among 28,779,982 candidates at odd orders 33–61 have a forbidden head-2 relation; 448 saturated tuples at 45 and 55 lack a unit, so the next generator reduction must use SHC rather than saturation alone |
| `SubtupleRigidity.lean`: `shc_deleted_span_eq_top` | assuming the lower-dimensional odd cyclic SHC bound, every coordinate deletion in the next strict window spans the ambient cyclic group |
| `SHCBaseCases.lean`: `cyclicSHCOddLowerBound_three`, `shc_four_deleted_span_eq_top` | kernel-reduced exclusions at orders 9, 11, and 13 prove the three-coordinate bound 15 and make four-coordinate deletion spanning unconditional through order 29 |
| `SHC.normalize_generator`, `not_exists_shc_of_normalized` | a generator coordinate can be reindexed and identified with `1` in `ZMod (|G|)`; a normalized finite exclusion then rules out the original SHC family |
| `SHCFourBaseCases.lean`: `normalized_shc_four_excluded_of_odd_window` | kernel-reduced sorted normalized exclusions for every odd modulus 17–29; dissociation plus the head-2 shell clause already contradict each other |
| `SHCFourGenerator.lean`: `cyclicSHCOddLowerBound_four`, `odd_min_five`, `shc_five_deleted_span_eq_top` | generator-coordinate existence at every odd order 17–29 closes the normalized reduction, proving the unconditional four-coordinate bound 31, G2 for valid five-tuples, and five-coordinate deletion spanning through order 61 |
| `SHCFiveGeneratorReduction.lean`: `shc_hasGeneratorCoordinate_zmod_five_of_odd_window_ne_forty_five` | subgroup-coordinate counts derived from the 15/31 cyclic SHC bounds force a generator at every odd order 33–61 except the unique tight partition at 45 |
| `SHCFiveGenerator.lean`: `shc_hasGeneratorCoordinate_zmod_forty_five`, `shc_hasGeneratorCoordinate_zmod_five_of_odd_window` | the tight order-45 `3+2` subgroup split is impossible by a quotient-pigeonhole contradiction to dissociation, completing generator-coordinate existence throughout the full five-coordinate strict window |
| `SHCFiveCertificate.lean`, `Generated/SHCFiveN*.lean`, `SHCFiveBaseCases.lean` | complete normalized five-coordinate window (33 analytically, every odd order 35–61 by generated certificates), the unconditional cyclic SHC bound 63, `odd_min_six`, and six-coordinate deletion spanning through order 125 |
| `SHCSixGeneratorReduction.lean`: `shc_hasGeneratorCoordinate_zmod_six_of_odd_window_ne_exceptions` | lower-dimensional SHC bounds force a generator coordinate at 27 of the 31 odd orders 65–125; the subgroup-cover method isolates exactly 75, 99, 105, and 117 as its tight exceptions |
| `SHCSixGenerator.lean`: `shc_hasGeneratorCoordinate_zmod_six_of_odd_window_ne_one_hundred_five` | quotient-pigeonhole contradictions close the tight two-prime cases 75, 99, and 117, proving generator-coordinate existence at 30 of 31 window orders; only the three-prime order 105 remains |
| `SHCSixExceptionalCertificate.lean`, `Generated/SHCSixN105*.lean`, `SHCSixGeneratorComplete.lean` | the exact-three subgroup argument reduces order 105 to 3,478,761 sorted normalized nonunit tails; 1,326 generated blocks use 208,601 kernel-checked decision-tree branches to exclude them, completing generator-coordinate existence at every odd order 65–125 |
| `SHCCardinality.lean`: `shc_card_ge_cube_add_two_doubles`; `SHCSixCardinality.lean`; `SHCSixCertificate.lean`; `Generated/SHCSixNormalizedN*.lean`; `SHCSixBaseCases.lean` | a uniform cube-plus-doubles injection proves `|G| ≥ 2^m + 2m` for every SHC family with `m ≥ 3`; the isolated analytic corollary closes the six-coordinate normalized window through 75 (6 of 31 odd cases), while the generated 67/69 certificates remain independent kernel-checked cross-checks; orders 77–125 and the full six-coordinate SHC bound remain open |
| `QuadraticWedge.lean`: `shc_diff_of_valid` | every valid anchored tuple satisfies SHC |
| `bottom_wedge_of_valid`, `quadratic_wedge_of_valid` | linear and quadratic wedges stated directly for valid tuples |
| `shc_shift_target_card_gt` | a $`2h_x`$ shift cannot increase subset-sum level |
| `GlobalRoadmap.lean` | defines `CriticalRangeCommonTouchedHalfWitnesses` and the weaker exact induction interface `CriticalRangeDeleteStep`; `critical_subsetSum_half_overlap_add_two_le` and `exists_light_half_witness_of_critical_range` quantify and populate the paired overlap family, while `criticalRangeDeleteStep_of_g1` records common touch as one deletion mechanism.  `stratum_lower_bound_of_deleteStep` and `global_lower_bound_of_deleteStep` prove the conditional lower bounds directly from deletion + G2 + G3; the original G1 theorem names remain backward-compatible wrappers. |
| `G1Counterexample.lean` | kernel-checks validity of `(172,41,658,861,601,286,875)` modulo `1006`, four half-witnesses with empty support intersection, and hence `¬ CommonTouchedHalfWitnesses`; also certifies that `1006` lies outside the seven-coordinate critical range |

The outstanding mathematical statements are the critical-range common-touch
theorem (G1), the complete odd-stratum lower bound (G2), and the exceptional
lift obstruction at $`2B(n-1)`$ (G3).  Unrestricted common touch is false and
is no longer an assumption of the conditional global theorem.

## Deviations from the paper proof

* **Theorem B** constructs the four witness representations directly by
  induction on bit-width with a parity split, instead of certifying them
  via `s_min`/popcount.
* **Theorem A** avoids popcount entirely and follows the paper's §5
  route directly. `gmin w M` (binary digits of `M` below bit `w`, plus the
  whole quotient on the top coin) is defined by the one-bit-peeling recursion
  `gmin (w+1) M = M % 2 + gmin w (M / 2)`, so every proof is an induction
  whose steps only use literal `/2`, `%2` — `omega` handles all arithmetic.
  `gmin_step` is the paper's Lemma 4 (subtraction encoded as
  `M' + 2^t = M + 2^{w+1}`), proved by bit-peeling with a parity split;
  `slack` iterates it over `j` from the base `gmin_ones`. No range
  restriction on `j`, no `Nat.log` case analysis, no small-`n` evaluations.
* Lemma 2 (`ones_unique`) is a descent on the bottom coin: parity forces
  `k 0 = 1 + 2t`, and `gmin_le_dsum` + `gmin_add_le` force `t = 0`.

## Formalization notes (kept for reference)

- `omega` treats `2^w` as an **opaque atom**, but *does* abstract nonlinear
  products (`j * N`) as atoms — provide bridging equations by `ring` and let
  omega finish linearly. Corners that are vacuous on paper via pow semantics
  need explicit case splits feeding omega the reduced facts.
- Mathlib v4.32 names: `Nat.lt_two_pow_self` (argument implicit),
  `Function.update_of_ne` / `Function.update_self`,
  `Nat.log_eq_of_pow_le_of_lt_pow` for concrete `Nat.log` values (does **not**
  reduce by `decide`). Note `Finset.range_subset` now means
  `range n ⊆ s ↔ ∀ x < n, x ∈ s`; the `range m ⊆ range n ↔ m ≤ n` form is
  `Finset.range_subset_range`.
- Goals of the form `val w (fun i => …) = …` are stated about a lambda;
  `rw`/`omega` need the beta-reduced shape — open such proofs with `show`,
  or reuse `shift_*` through a pointwise `Finset.sum_congr`.
