# Prove2Me mission and maintained DAG

The owner launched **The min-modulus conjecture for unique multiset sums**
as a private mission on 2026-09-10. Open [My missions](https://prove2.me/my-missions).
Mission ID: `6b060afa-1e7b-4c80-8f4a-cc89ff36784e`.
Goal theorem ID: `67fbce28-44f4-45cb-8e37-de63df56557c`.

The [platform DAG package](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/platform-dag)
records 39 proved supporting nodes, accepted reductions, exact source hashes,
server theorem/submission IDs, and the complete root frontier. The goal's
three open leaves are:

- `MinModulus.primitive_three_omission_delete_step` (current G1 residual).
- `MinModulus.odd_stratum_lower_bound` (G2).
- `MinModulus.exceptional_quantitative_escape_obstruction_from_six` (current G3 residual, n≥6).

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
341 nodes and 840 edges, with an acyclicity audit. Both supporting milestones
are complete. The whole mission frontier now consists of primitive G1, G2
and quantitative G3 for n≥6. Seven additional primitive supporting statements
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
equivalent n≥5 restriction after discharging n=3, and now to n≥6 after
discharging the full n=5 case modulo 24. Both changes and their
reasons are recorded in platform history. Original G3 remains an Open parent. Across all six bundles, the consolidated audit verifies 199
proof dependency sets and all 192 source nodes are Proved. No research gate
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
`ExceptionalQuantitativeEscapeObstructionFrom 6` on Prove2Me. The current
leaf is `c18a7a8e-12c6-4c36-bd3c-8e1c29d290fc` and the accepted parent bridge is
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
has 341 nodes and 840 edges, with the same three research branches.

## New local four-coordinate G1 refinement

The full four-coordinate cyclic bound and every exact stratum now hold in
`FourCyclicLowerBound.lean`. The proved equivalence reduces primitive G1 to
`PrimitiveThreeOmissionDeleteStepFrom 4`, whose parent length is at least
five. This local result does not yet change the platform frontier above;
that requires supported verification and an accepted connecting reduction.

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
