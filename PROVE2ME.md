# Prove2Me mission and maintained DAG

The owner launched **The min-modulus conjecture for unique multiset sums**
as a private mission on 2026-09-10. Open [My missions](https://prove2.me/my-missions).
Mission ID: `6b060afa-1e7b-4c80-8f4a-cc89ff36784e`.
Goal theorem ID: `67fbce28-44f4-45cb-8e37-de63df56557c`.

The [platform DAG package](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/platform-dag)
records 39 proved supporting nodes, accepted reductions, exact source hashes,
server theorem/submission IDs, and the complete root frontier. The goal's
three open leaves are:

- `MinModulus.primitive_three_omission_delete_step_from_five` (current G1 residual, parent length ≥6).
- `MinModulus.odd_stratum_lower_bound` (G2).
- `MinModulus.exceptional_quantitative_escape_obstruction_from_seven` (current G3 residual, n≥7).

G1 first reduced to its two-large-parity-fibres restriction. The accepted
[primitive refinement](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/primitive-dag)
now narrows that residual through dimension induction, retaining the same
G2 and G3 assumptions and discharging the child-bound premise internally.
The main reduction preserves the mission's original validity definition and exact
conjecture statement. Conjecture 1 and all three research inputs remain open.
The original finite-abelian lower-bound milestone is now Proved on the
platform, using the uploaded subset-sum injectivity theorem. Its exact local
type check and server receipt are in the companion
[proof bundle](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/milestones/abelian-lower-bound).
The [canonical-family minimum](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/canonical-dag)
is also Proved, using 22 additional proved source statements and two checked
validity-model bridges. All 23 solutions match their exact targets after a
local supported-environment build of 8,759 jobs. Its source port retains 42
declarations in four modules without proof-body changes; 41 original types
match literally, and one set-constructor alias is checked definitionally.

The expanded DAG across the goal and all five mission milestones contains
430 nodes and 1032 edges, with an acyclicity audit. Both supporting milestones
are complete. The whole mission frontier now consists of primitive G1, G2
and quantitative G3 for n≥7. Seven additional primitive supporting statements
are Proved. Their exact platform files built 8,738 jobs; all seven source types and eight solution types match.
The source port has 105 declarations with literal type matches and standard
axiom audits. The primitive input and the original G1 parent both remain
Open. The accepted
[G3 quantitative reduction](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/g3-dag)
now adds 114 Proved source nodes and 115 checked solutions. Its 242-declaration
source slice retains 241 original bodies byte for byte, with 241 literal types
and one checked set-constructor alias. All 114 platform source types match
literally. The exact upload build passed 8,960 jobs, all four new definitions
passed axiom audits, and all 115 private statements were read back exactly.

The first G3 refinement retained every original dimension and the
collision-inclusive all-shift bounds. The milestone first moved to the
equivalent n≥5 restriction after discharging n=3, then n≥6 after excluding
the n=5 case modulo 24, and now n≥7 after excluding n=6 modulo 56. These changes and their
reasons are recorded in platform history. Original G3 remains an Open parent. Across all nine bundles, the consolidated audit verifies 259
proof dependency sets and all 249 source nodes are Proved. No research gate
is proved. The [dimension-three refinement](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/g3-large-dag)
adds three Proved source nodes and four accepted solutions. The new
`exceptionalQuantitativeEscapeObstruction_iff_large` equivalence uses the
known three-coordinate exclusion modulo four to leave the intermediate n≥5
quantitative G3 obligation. Its supported platform build passed 8,723 jobs,
with three literal source types, four independently checked solution types
and one definition axiom audit. The original and preceding quantitative G3
parents remain in the DAG, and the milestone history records the reduction.

## Verification and coverage

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
