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
- `MinModulus.large_exceptional_quantitative_escape_obstruction` (current G3 residual, n≥5).

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
326 nodes and 807 edges, with an acyclicity audit. Both supporting milestones
are complete. The whole mission frontier now consists of primitive G1, G2
and quantitative G3 for n≥5. Seven additional primitive supporting statements
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
collision-inclusive all-shift bounds. The milestone now points to the
equivalent n≥5 restriction after discharging n=3. Both changes and their
reasons are recorded in platform history. Original G3 remains an Open parent. Across all five bundles, the consolidated audit verifies 191
proof dependency sets and all 185 source nodes are Proved. No research gate
is proved. The [dimension-three refinement](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/g3-large-dag)
adds three Proved source nodes and four accepted solutions. The new
`exceptionalQuantitativeEscapeObstruction_iff_large` equivalence uses the
known three-coordinate exclusion modulo four to leave exactly the n≥5
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
