# G2 reduces to absolute bounds at the two central degrees

[AbsoluteRepeatedCoinBounds.lean](AbsoluteRepeatedCoinBounds.lean) proves
a generic reduction that does not assume growth between successive coin
degrees. Write D_k for the repeated degree-k coin values of a valid tuple.
It suffices, at k=floor(n/2) and k=ceil(n/2), to prove

    sum_{j=0}^{k-1} choose(n,j) <= |D_k| + 1.

For positive k this says |D_k| >= sum_{j=1}^{k-1} choose(n,j).
The required lower bound is an explicit binomial sum; it does not depend
on the actual size of the preceding coin cover.

Four theorems are proved:

* The absolute bound holds through degree three, using the already proved
  first two growth steps.
* The two central absolute bounds imply the sharp odd-modulus lower bound.
  The exact squarefree/repeated decomposition supplies central coin-cover
  bounds, and complementary packing combines them. Oddness improves the
  resulting N >= 2^n-2 to N >= 2^n-1.
* Every odd counterexample violates the absolute bound at a central degree
  k >= 4. This narrows the necessary failure from an arbitrary earlier
  growth step to one of the two central degrees.
* Establishing these central absolute bounds from degree four onward for
  every valid odd tuple would prove the entire odd stratum, G2.

All four original proof bodies pass both Mathlib revisions with eight
exact printed types, four unchanged definition values and standard axioms.
The proof is uniform in n and uses no finite search. The three small
degrees are symbolic base cases of the reduction.

The central absolute bounds from degree four onward remain unproved.
The quartic half-fibre bound does not by itself supply them. G1, G2 and
G3 remain open. These four new reduction statements await platform export
and upload.

## Verified four-theorem central-degree export

All four central-degree reductions now have a verified split export.
Both revisions pass all four exact original types and dependency sets,
four definition comparisons and fourteen exact inline helper types.
The local subsetCoinSums helper definition also matches its original
value. All four original proof bodies and all inline helper bodies are
retained. Four existing Proved interfaces and existing definitions are
reused; no new server definition bundle is introduced. The proof of the
uniform conditional G2 reduction is the terminal supporting root.
Metadata and live preflight pass. These four nodes have not yet been
uploaded. The uniform central absolute bounds and G1/G2/G3 remain open.
