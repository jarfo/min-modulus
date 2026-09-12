# Parallel G2 log review, 12 September 2026 at 14:41 UTC

The latest reviewed Claude session has moved from anchored-overlap multipliers
to the proper-subset SDR proposal. The older multiplier draft was deleted
because the verified research files supersede it. Its corrected relation-free
count is 605 occurrences; the earlier 632 was an overcount.

The unrestricted SDR proposal in dimensions at least seven is already refuted
by [AnchoredSDRCounterexample.lean](AnchoredSDRCounterexample.lean): the valid
tuple (0,41,97,107,110,215,251) modulo 329 has two different six-subsets whose
only available representative is 51. Both supported and original Lean builds
and their type/axiom audits are archived. This does not refute G2, or an SDR
claim restricted to hypothetical moduli below 2^n-1.

The newer search reports no valid six-sets at primes 67,71,73, and respectively
60,210,720 normalized valid six-sets at primes 79,83,89, all passing SDR.
All six counts match our independently archived exhaustive search. The new
SDR results themselves are computational reports, not new Lean proofs.

The last log starts a normalized seven-set search at 127,131,137; it contains
no result for that run yet. Its referenced background output file is absent
in this environment. Our earlier independent completed search already found
6 normalized valid seven-sets at 127 and none at 131 or 137. These are
computational classifications, not Lean exclusions or a general G2 proof.

The code needs explicit completion reporting: its node-budget exit can print
the same summary as an exhaustive run. The six-dimensional node counts above
are below its 60,000,000 budget. Earlier pool-capped samplers can miss every
valid tuple, including the canonical tuple at 127, and cannot prove absence.

The suggestion that SDR failures cluster at composite moduli agrees with our
seven-dimensional sample: all 40 failures occur at composite moduli. It is
still a sample observation. SDR at all primes remains unproved, and would
leave composite odd moduli in G2 unresolved.

No new commit is available on origin/prove2me-001: its checked head remains
7e717f5bae6dfe8a5c80d9617b74d1532b2bb70c. No new theorem node is uploaded by
this review. G1, G2, G3 and the full conjecture remain open.

[Public log excerpts, code and count comparisons](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-sdr-seven-research).
