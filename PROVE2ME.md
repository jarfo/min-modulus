# Prove2Me mission and maintained DAG

The private mission **The min-modulus conjecture for unique multiset sums**
is available under [My missions](https://prove2.me/my-missions).
Mission ID: `6b060afa-1e7b-4c80-8f4a-cc89ff36784e`.
Goal theorem ID: `67fbce28-44f4-45cb-8e37-de63df56557c`.

The current consolidated DAG has 472 nodes, 1123 edges and exactly three
open leaves. Its 277 source nodes across ten bundles are Proved, and all
288 proof dependency sets match compiler records and accepted reductions.
The finite-abelian and canonical-family milestones are Proved. The
unrestricted conjecture and all three research gates remain Open.

- G1: `MinModulus.primitive_three_omission_delete_step_from_five`, for parent lengths at least six.
- G2: `MinModulus.odd_stratum_lower_bound_from_six`, for tuple lengths at least six.
- G3: `MinModulus.exceptional_quantitative_escape_obstruction_from_seven`, for dimensions at least seven.

The parallel branch `prove2me-001` at
`a3f0ebe423455ac8edae01663f87f35a61957dbd` proves every odd-modulus case
through dimension five. Its 27 new source theorems and the newly published
adapter for the existing cardinality bound are Proved. Accepted reduction
`30e0673e-abf8-43ce-9adf-c121953fd403` connects the original G2 parent to
the proved equivalence and the new open leaf
`cbc1224a-b0c0-4642-b405-5c8fde522e5f`. The milestone history preserves
this equivalent replacement. This is the parallel agent's next target.

The exact branch source compiles unchanged. The integrated full project
passes 15,504 jobs and a 6,129-declaration axiom audit. The supported
source port passes 8,715 jobs, 104 literal type matches and standard-axiom
checks in eight modules, preserving all 89 selected whole commands.
All 28 published source types match literally. All 29 exact accepted
solutions have matching target types and actual server dependency sets;
98 definition declarations pass the standard-axiom audit.

The companion [G2 proof bundle](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/g2-small-dag)
and [source port](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/g2-small-port)
preserve exact files, hashes, compiler records and server receipts.
The [consolidated DAG](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/platform-dag)
includes the goal and all five captain milestones and passes acyclicity,
frontier and whole-mission dependency audits.

The six-coordinate even-stratum publication is still in progress; G1
remains at its accepted parent-length-six leaf until all submissions and
the resulting DAG are verified. Recent source cycle-descent lemmas also
need accepted connecting proofs before they change the platform frontier.

After each verified milestone, update the private platform, run
`platform-dag/scripts/refresh_verified.py`, update these records, and
commit and push both repositories before continuing. Independent agents
use separate checkouts; one coordinator maintains the consolidated DAG.

## Earlier verification and coverage

The records below retain the build results and snapshots of earlier
milestones. The current frontier and counts are given above.

The supported platform environment is Lean 4.33.1 with Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`. This proof repository retains
its existing pins. The compact source port contains 102 declarations in 21
modules from commit `b615a8bbc7fb52a7700f5b8d2c6b89f86c807efb`: all 102
original types and axiom audits passed without proof-body changes.

The final platform split built 8,797 jobs. Its 39 source theorem types match
after canonicalizing universe names (38 also match without that step), all
41 independent solutions match their target types, and all 23 bundled
definition declarations pass the standard-axiom audit. Server verification
establishes the accepted graph edges.

The [DAG plan](https://github.com/jarfo/unique/blob/main/papers/min-modulus/prove2me/dag-plan.md)
also records the primitive and quantitative refinements of the same three
gates. Their full source closure reaches 19,760 declarations in 725 modules,
including generated declarations; they have not all been ported. Recent
strict-growth and escape-density results need a further argument connecting
them to an open gate. The unrestricted common-touch assertion is false and
must not reappear as an open sufficient lemma.

## Accepted five-coordinate G3 refinement

`not_validTuple_five_mod_twenty_four` excludes the complete n=5 exceptional
case. Its proved equivalence now connects the preceding n≥5 G3 input to
`ExceptionalQuantitativeEscapeObstructionFrom 6` on Prove2Me. At that stage the
leaf was `c18a7a8e-12c6-4c36-bd3c-8e1c29d290fc` and the accepted parent bridge is
`e6d19aef-88ad-430a-b878-0618b6578106`. The G3 milestone and its history reflect this replacement.

The full original build passed 15,413 jobs and the axiom audit covers 5,363
declarations. The supported source port has 40 literal type matches and
standard-axiom audits, with all 34 source command bodies byte-identical.
The exact platform build passed 8,736 jobs; all seven source types and eight
solution types match, and all 13 new definition declarations pass axiom
audits. The coverage theorem uses kernel evaluation and has no axioms.
All seven new source nodes are Proved. The new G3 input remains Open.

The [platform bundle](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/five24-dag)
preserves the accepted receipts, exact statement readbacks, dependency audit,
supported source evidence, and milestone history. The consolidated mission
has 430 nodes and 1032 edges, with the same three research branches.

## Accepted four-coordinate G1 refinement

`FourCyclicLowerBound.lean` proves the unrestricted positive cyclic bound
12≤N and every exact two-adic stratum for valid four-tuples. Its equivalence
now reduces primitive G1 to `PrimitiveThreeOmissionDeleteStepFrom 4` on
Prove2Me: child dimension at least four and parent length at least five.
At that milestone the leaf was `7f5a692e-58b4-4ef1-807c-27b2dc4a7c12` and the accepted parent bridge
is `5a1e0170-34ad-4b45-b6ad-fe769d3b3615`. The milestone and its history record the replacement.

The full original build passed 15,416 jobs and its axiom audit covers 5,379
declarations. The supported source port has 70 literal type matches and
standard-axiom audits, with all 53 source command bodies byte-identical.
The exact platform build passed 8,745 jobs: ten source types match (nine
literally, one after a checked bound-universe rename), all eleven solution
types match, and all three new definition declarations pass the axiom audit.
All ten new source nodes are Proved. The remaining G1 input is Open.

The [platform bundle](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/four10-dag)
preserves exact readbacks, accepted receipts, type and axiom evidence,
source hashes, the dependency audit, and milestone history. The complete
consolidated mission has 430 nodes and 1032 edges and the same three
research branches. G2 is the selected parallel-agent assignment.

## Accepted five-coordinate even-stratum refinement

`FiveEvenCyclicLowerBound.lean` proves every positive exact two-adic stratum
for valid five-tuples: bound 30 at valuation one and 28 at higher valuations.
The equivalence in `G1FiveCoordinateBase.lean` reduces P(4) to P(5), so the
remaining G1 input has parent length at least six. Its current theorem is
`ae79dd8a-6831-472d-98ed-3c562de4cc13` and the accepted bridge is `ea93c82c-2d79-4e7f-be01-809ea2bb3a9f`.
The milestone replacement and its reason are saved in platform history.

The full original build passed 15,419 jobs and the complete axiom audit
covered 5,400 declarations. The supported source port has 68 literal type
matches and all 60 selected source command bodies unchanged. The exact
platform build passed 8,744 jobs, with nine literal source type
matches, ten independently matching solution types and six passing
definition axiom audits. All four numerical coverage proofs are axiom-free.
All nine new source nodes are Proved and all ten submissions have accepted
verdicts. Sixteen existing theorem IDs and eight definition bundles are reused.

The [accepted bundle](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/five-even-dag)
retains exact readbacks, receipts, source hashes, type/axiom evidence and
complete branch snapshots. The consolidated mission has 379 nodes and
927 edges; all 211 source nodes across eight bundles are Proved and all
220 proof dependency sets pass the audit. G1, G2, G3 and the conjecture remain
Open. G2 is the selected independent parallel-agent assignment.

## Accepted six-coordinate G3 refinement

The complete six-coordinate exclusion modulo 56 is accepted on Prove2Me.
The G3 leaf is `MinModulus.exceptional_quantitative_escape_obstruction_from_seven`
(`871bd599-0124-4e97-ba23-2278e25c515e`), retaining every quantitative premise for non-power-of-two
dimensions n≥7. Bridge `c8d15a16-56d7-4514-bdc4-e17eacaf887e` consumes the reverse direction
of the proved Q(6)↔Q(7) equivalence. The preceding Q(6) theorem remains an
Open parent. G1, G2, G3 and the unrestricted conjecture remain Open.
G2 is the selected independent parallel-agent assignment.

At source commit `69e799885b283db093c9ed54fb79548c19b42ac5`, the original
build passed 15,455 jobs and its axiom audit covered 5,450 declarations. The supported source port passes 8,752 jobs, with 114 literal
type matches and 81 preserved source commands across 45 modules. The exact
platform package passes 8,802 jobs, with 38 source type matches,
39 solution type matches and 15 definition axiom audits. Its 26 row proofs
and final direct block are axiom-free. Six block reductions consume accepted
row statements; all 33 complete source row/block theorems are axiom-free.

The [accepted bundle](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/six56-dag)
retains the resource-error history, source, readbacks, accepted submissions
and dependency evidence. The consolidated mission has 430 nodes and
1032 edges. All 249 source nodes across nine bundles are Proved, and all
259 proof dependency sets pass the audit.

## Continue after each verified milestone

Build new statements and proofs on a currently supported platform revision,
compare their source types and audit their axioms, then publish any new
prerequisites and submit the checked proof or reduction. Retain the private
visibility. Accepted reductions supply dependencies; milestone ordering
supplies an attack order. Choose one direction when using an equivalence so
the proof graph remains acyclic.

Refresh the goal graph and every page of its open leaves, update the source
commit and theorem/submission IDs, and commit and push both repositories.
Then continue with a connected open obligation, considering closability,
tractability and reuse. Run `platform-dag/scripts/refresh_verified.py` in the
companion bundle to refresh the consolidated graph and require all dependency
audits to pass. Credentials remain in the user's external Prove2Me workspace.

The original four-item proposal, independent blind readbacks, and initial
8,716-job statement build are preserved in the
[initial bundle](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me).

## Verified six-coordinate even-stratum source

The six-coordinate even-stratum source milestone now proves `60 ≤ N` for
every valid six-tuple at a positive even modulus, and the exact-stratum
bounds 62 at valuation one and 60 at higher valuations.
`primitiveThreeOmissionDeleteStepFrom_five_iff_six` removes parent length six
from G1. The original build passed 15,498 jobs and the complete
axiom audit checked 6,079 declarations. The supported Lean 4.33.1
source port passed 8,794 jobs, with 762 literal type matches and
727 byte-identical command bodies in 87 modules.
The exact platform statement/solution package and accepted submissions remain
pending; the accepted G1 leaf stays at P(5) until that work passes. G2, G3
and the unrestricted conjecture remain open.

## Verified sharp Mersenne charge

The new `G1MersenneCharge.lean` sharpens the uniform quotient-charge
factor from `2^(b+1)` to `2^(b+1)-1` when at least two coordinates remain,
and proves sharpness at valuation one with two retained coordinates.
At Mersenne order, failed charge now forces cycle length `d ≤ b`, improving
the previous `d-1 ≤ b` boundary. Eight new lemmas connect this to the
existing doubling rigidity and full-cycle descent. The full source build
passed 15,499 jobs and 6,087 axiom audits; the supported port passed
8,723 jobs with 46 literal type matches and 46 unchanged complete commands.
This source refinement is not yet uploaded and does not close a research gate.

The [supported source port](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/mersenne-charge-port)
preserves both-revision builds, compiled statements, source-command
comparisons, and axiom audits. The accepted platform frontier is unchanged.

## Constructed exact Mersenne descent

`G1ExactMersenneDescent.lean` now constructs the sharpened descent from
an actual valid doubling subtuple. Each cycle coordinate generates the
entire leaf span with exact order `2^d-1` dividing the odd factor. The
construction chooses the minimal transversal and retains its quotient and
private witnesses; a direct adapter uses the existing saturated G1 leaf
algebra. The full source build passed 15,500 jobs and 6,090 axiom audits;
the supported port passed 8,733 jobs, with 83 literal type matches and
83 unchanged complete commands. The failed-charge branch remains open,
and these three new source lemmas are not yet uploaded.

The [supported source port](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/exact-mersenne-descent-port)
retains the complete verification evidence. The accepted platform
frontier is unchanged.

## Descent supported on the cycle

`G1CycleSupportedDescent.lean` now chooses the minimal kernel-witness
transversal inside the actual affine doubling cycle. If charge fails,
the chosen deletion set equals the whole cycle; it contains no outside
coordinate. A direct adapter uses the saturated G1 leaf algebra. The
full source build passed 15,501 jobs and 6,095 axiom audits;
the supported port passed 8,740 jobs with 104 literal type matches
and unchanged complete commands. The whole-cycle deletion case remains
open. These five source lemmas are not yet uploaded.

The [supported source port](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/cycle-transversal-port)
retains the verification evidence. The accepted platform frontier
is unchanged.

## Recursive cycle descent with an outside involution

`G1InvolutionCycleDescent.lean` proves recursive descent for an actual
affine doubling cycle beside an outside coordinate annihilated by two
after translation. Deleting all but one cycle coordinate already meets
every nonzero kernel witness, so a minimal deletion set has size below
the cycle length and the sharp Mersenne charge always succeeds. The
saturated leaf-permutation adapter supplies the involution from its star
center. The full build passed 15,502 jobs and 6,102 axiom audits;
the supported port passed 8,743 jobs with 119 identical types and
complete commands. The operational global-star case was already closed
by `G1PureStarElimination.lean`; the new general cycle result does not
close the remaining main G1 gates. These seven lemmas are not yet uploaded.

The [supported source port](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/involution-cycle-port)
retains the verification evidence. The accepted platform frontier
is unchanged.

## Seven-coordinate exclusion modulo 66

`SevenModSixtySix.lean` proves that no valid seven-coordinate tuple exists
modulo 66. It combines 129 kernel-checked certificate rows in 56 independent
modules, using affine normalization when a unit difference exists and a
separate nonunit-pair certificate otherwise. Generic prefix soundness lemmas
cover every sorted extension. The final original build passes 15,567 jobs
and 6,417 axiom audits; the supported port passes 8,777 jobs with 474 literal
type matches and 450 byte-identical complete commands. This is one finite
modulus, not the full seven-coordinate even bound. G1/G2/G3 remain open;
these new source results are not yet uploaded to Prove2Me.

The [supported source port](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/seven66-port) retains the verification evidence.

## G3 reduction from dimension seven to nine

`SevenModOneTwenty.lean` excludes valid seven-coordinate tuples modulo
120. `G3SevenModOneTwenty.lean` consequently proves the equivalence between
the G3 inputs from dimension seven and from dimension nine. The proof uses
minimal affine representatives, 324 independent kernel-checked certificate
blocks and 63 assembly modules. The original build passes 15,959 jobs and
9,383 axiom audits; the supported port passes 9,111 jobs with 5,914 literal
type matches and 5,894 byte-identical complete commands. G1/G2/G3 and the
full conjecture remain open. These results are not yet uploaded to Prove2Me;
the accepted platform G3 leaf remains From7.

The [supported source port](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/seven120-port) retains the verification evidence.

## Parallel anchored-union proposal review

The latest parallel branch update, `d3ef872`, adds the conjectural
anchored-union bound and a checked implication from it to G2. Its four
declaration types match on the original and supported Lean revisions; the
integrated project passes 15,960 jobs and 9,384 axiom audits. The conjectural
bound itself remains open and is not an accepted G2 reduction. Fresh platform
reads confirm all 29 earlier G2 submissions remain accepted and the only G2
open leaf is still the odd-stratum lower bound from dimension six.

The [independent review](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/g2-anchored-review) preserves exact proof checks and fresh server readbacks.

## Bounded modulo-58 verification

The two largest stalled modulo-58 rows now use 33 independent interval
proofs, each covering at most 2,000 sorted tails. Their original statements
are unchanged. The full original build passes 15,994 jobs and 9,417 axiom
audits; all 35 affected types and exact platform proofs pass supported Lean
checks. The six-even publication can reuse every accepted submission and
replace only the two timed-out proofs. Platform acceptance remains pending.

The [supported proof package](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/six58-parts-port) records the source and platform checks.

## Parallel G2 recheck (2026-09-11 21:11 UTC)

Remote and local parallel branch `prove2me-001` remain at `d3ef872`, already
merged into `descent`; the parallel checkout has no uncommitted changes.
Fresh server reads confirm 28 accepted proofs and one accepted reduction,
with `OddStratumLowerBoundFrom 6` still the sole G2 leaf and no submissions
on that leaf. Its milestone is already linked correctly.

The separate exploration scripts are now available for review. Independent
finite checks reproduce the valid tuple `(0,28,12,22,7)` modulo 30 with
anchored union size 29, a counterexample to the proposed even extension.
The bounded clique search does not justify the live discussion's claim
that every fixed-family proof is impossible. The odd anchored-union bound
and G2 remain unproved. See the [fresh review and reproducible evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/g2-anchored-review/recheck-20260911T211122Z).

## Bounded modulo-120 DAG preparation

`SevenModOneTwentyBundles.lean` groups 2,883 verified prefix certificates
into 324 proposed DAG nodes: 252 conjunctions and 72 reused singleton
statements. All 252 new types and all 2,883 component projections pass on
both Lean versions. The integrated original build passes 15,995 jobs and
9,669 axiom audits. No original proof or statement changed.

These are locally verified source bundles; exact platform conversion and
publication remain pending. The accepted G3 frontier is still From7.
See the [bundle evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/seven120-bundles).

## Exact modulo-120 platform verification

The G3 split now builds against supported Lean 4.33.1 / Mathlib `0df444a3`:
401 source statements match their original compiled types literally, all
402 solutions pass independent type/axiom/dependency checks, and 19 generic
definition commands have only standard axioms. The final Lake pass completed
9,532 jobs in 13m37s with previously built dependencies and statements.

The package retains 324 bounded certificate nodes for 2,883 components and
77 generic/assembly nodes. Exact source and payload hashes, parser evidence,
and 6,122 unchanged source slices are preserved in the
[local platform package](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/seven120-platform).
Publication is pending; the accepted G3 frontier remains From7 and the full
conjecture remains open.

## General sparse targets beside an actual Mersenne cycle

`CycleSparseTargets.lean` extends the outside lifting argument to arbitrary
integer coefficient vectors bounded below by -1. A positive total k smaller
than the cycle length can hit its subgroup only at a sum of fewer than k
cycle entries. The total-one and total-two cases follow without a support
restriction. All four types and axiom audits pass on both Lean revisions;
the full project passes 15,996 jobs and 9,673 axiom audits.
These are local structural results, not a discharge of a research gate, and
have not been uploaded. See the
[proof evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/cycle-sparse-targets).

## Bounded modulo-58 row-5 revision

Modulo-58 row 5 now uses 15 bounded interval certificates after two
server verification timeouts. They cover 22,100 sorted tails, at most 1,946
per part; the original row statement and other row proofs are unchanged.
All 16 affected types match across both Lean revisions and the platform
statements; all 16 exact platform proofs and dependency checks pass. The full original project passes 16,011
jobs and 9,688 axiom audits. All 216 accepted submissions
are retained; the revised six-even publication remains pending.

See the [verification package](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/six58-row5-port).

## Exact short-sum rigidity and unique sparse targets

`CycleShortSumRigidity.lean` proves exact short-sum rigidity for valid
zero-sum families closed under doubling predecessors. Proper subset sums
are uniquely shortest, and their small-subset sumsets have exact binomial
cardinality. For an actual Mersenne cycle, the shortened-cover obstruction
is an equivalence, and each outside surplus target has a unique small
cycle support. All six types match on both Lean revisions; the integrated
project passes 16,012 jobs and 9,694 axiom audits.
The cycle remains an input and repeated expansion remains open; these
results do not discharge G1, G2, G3 or the full conjecture.

The new lemmas are not uploaded. See the [verification package](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/cycle-short-sum-rigidity).
