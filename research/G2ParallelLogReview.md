# Parallel G2 log review, 12 September 2026 at 15:35 UTC

The parallel branch fast-forwarded to descent commit a43fdfe8 and pushed it.
The remote head was checked directly. Its history is already contained in
descent, so there is no additional proof commit to merge.

The parallel agent independently confirmed the dimension-seven counterexample
in [AnchoredSDRCounterexample.lean](AnchoredSDRCounterexample.lean). The tuple
(0,41,97,107,110,215,251) is valid modulo 329; the two six-subsets omitting 110
and 251 each have only the anchored value 51. The unrestricted proper-subset
SDR proposal therefore fails in the live dimension range. The parallel notes
now acknowledge this. It does not refute G2 or a proposed SDR statement
restricted to hypothetical moduli below 2^n-1.

The completed normalized seven-set search reports six valid sets at 127,
all satisfying SDR, and no valid sets at primes 131 and 137. All three counts
match our independent completed computation. The reported node counts
7,581,001, 9,606,656 and 13,628,484 are below the supplied search budget.
At primes every nonzero difference is a unit, so normalization loses no
affine class. These are computational classifications, not new Lean proofs.

The composite runs at 129 and 133 report no normalized valid seven-set,
after 9,182,156 and 10,829,135 nodes. Normalization to contain 0 and 1 covers
only tuples having a unit difference. These results do not exclude tuples
with no unit difference. The logs also do not show a completed run at 135,
so they do not justify the broader statement that only 127 admits any
valid seven-set throughout the whole odd interval 127 through 137.

The parallel agent now recommends half-degree coin growth and the anchored
overlap criterion as the remaining general approaches. The implication from
half-degree growth to G2 is verified in
[HalfDegreeCoinGrowth.lean](HalfDegreeCoinGrowth.lean); its growth hypothesis
remains unproved. The anchored criterion also still needs a suitable general
existence or counting argument. Neither recommendation closes G2.

Earlier findings remain: the corrected relation-free count is 605 occurrences
(the earlier 632 was an overcount); six-set counts at primes 67,71,73,79,83,89
match our exhaustive search. All 40 SDR failures in our seven-dimensional
sample have composite modulus, but a prime-only SDR theorem remains open.

This review adds no Lean theorem or Prove2Me proof node. G1, G2, G3 and the
full conjecture remain open.

[Mathematical outputs and independent count comparisons](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-sdr-seven-research).
