# Averaging does not repair the anchored overlap bounds

The existing Lean-verified valid tuple (0,11,8,6) modulo 15 already
refutes averaged versions of the pairwise-quarter and triple-eighth
proposals. No new tuple search or finite-modulus exclusion is needed.

For its four anchored cubes, in lexicographic anchor order:

* The six pair intersections have sizes 5,3,4,4,5,4. Their sum is 25,
  exceeding choose(4,2)*2^(4-2)=24.
* The four triple intersections have sizes 2,3,1,3. Their sum is 9,
  exceeding choose(4,3)*2^(4-3)=8.
* Every distinct pair intersects in more than one point. Thus universal
  existence of a pair meeting only at zero is also false.
* The union still consists of all 15 residues, exactly the conjectured
  sharp odd bound.

`AnchoredMomentCounterexample.lean` defines the r-th intersection moment
as the sum over r-element sets of anchors and proves the two exact totals,
the all-pairs assertion, and a combined counterexample theorem. It reuses
the previously proved control and validity definition. Both revisions pass
ten type comparisons, five definition-value comparisons and the standard
axiom audit. The control source is compiled again on both revisions.

These results rule out the displayed unconditional shortcuts, not G2.
The weaker claim that some pair has intersection at most a quarter is
not refuted: this example has a pair of size three. The example is at
N=2^n-1, so it does not refute a relation-free-pair statement restricted
to hypothetical counterexamples with N<2^n-1. That restricted statement
remains an unproved possible sufficient condition.

The supporting probe checks moments on 770 already saved valid examples
of dimensions four through ten. It is only a diagnostic on that dataset;
the formal conclusions above use the single previously verified control.

The earlier critical-range machinery remains relevant. In particular,
`G1OverlapCriticality.lean` already proves the exact identity
N+overlap=2^n+uncovered, so an overlap lower bound must not replace the
actual modulus hypothesis or silently discard uncovered residues.
The weighted-witness contradiction remains missing. All generic gates
and the arbitrary-n conjecture remain open.
