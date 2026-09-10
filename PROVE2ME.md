# Prove2Me mission draft

The draft **The min-modulus conjecture for unique multiset sums** was created
on 2026-09-10. It is available in [My missions](https://prove2.me/my-missions)
under proposal ID `e0c1179a-b95d-496d-b2ae-d1788fcb3447`.

The reproducible statement bundle, exact uploaded payloads, independent
readbacks, and server receipts are in the companion repository:
[Prove2Me bundle](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me).

Before upload, the definition, three open theorem statements, and separate
proof-based model checks passed a complete local build (8,716 jobs) using
Lean `leanprover/lean4:v4.33.1` and the supported Mathlib revision
`0df444a360eaa60ab8c11dca51a86af692955474`. The server readback confirms
four items, two supporting milestones, and unpublished **Draft** status.

The goal is Conjecture 1 for arbitrary distinct valid tuples in positive
cyclic moduli. The two supporting milestones are the known finite-abelian
lower bound and the exact canonical-family minimum. The draft theorem
placeholders are statement declarations, not proofs. Conjecture 1 and the
unrestricted G1/G2/G3 proof obligations remain open.

The independent statement package uses the Prove2Me environment; this proof
repository retains its existing Lean and Mathlib pins. Its formal proofs
remain subject to the repository's complete build and axiom audit.

## The dependency frontier

The companion [DAG plan](https://github.com/jarfo/unique/blob/main/papers/min-modulus/prove2me/dag-plan.md)
records how the existing conditional theorem connects Conjecture 1 to
`CriticalThreeOmissionDeleteStep`, `OddStratumLowerBound`, and
`ExceptionalLiftObstruction`. These are open assumptions, with proved
conditional reductions between them and the goal. G1 further reduces to its
existing two-large-parity-fibres residual.

A Lean meta-program extracted the proof dependencies at commit
`b615a8bbc7fb52a7700f5b8d2c6b89f86c807efb`: the conditional root plus the G1
parity equivalence reaches 102 declarations in 21 modules. The
[dependency excerpt](https://github.com/jarfo/unique/blob/main/papers/min-modulus/prove2me/source-dependency-slice.json)
contains selected exact records and pinned source links. The recent
escape-density results are not yet dependencies of that conditional proof;
connecting them to a gate requires a further argument.

On Prove2Me, accepted reductions establish graph edges; milestones only
specify an attack order. Once the draft is live, select work from the root's
`open-leaves` endpoint, using closability, tractability, and relevance to
these open gates. The local conditional reduction still needs to be ported
to the supported platform environment before submission.

Further checked reductions refine G1 to the primitive deletion residual and
then refine all three gates to quantitative escape inputs. The final source
assembly is `global_lower_bound_of_three_quantitative_escape_inputs` in
`G3QuantitativeEscape.lean`. Its dependency closure is acyclic and reaches
19,760 declarations in 725 modules, including generated declarations. The
DAG plan therefore stages the compact initial route first and records the
narrower frontier for later transfer. Equivalences supply one chosen
reduction direction; they must not create circular proof dependencies.
