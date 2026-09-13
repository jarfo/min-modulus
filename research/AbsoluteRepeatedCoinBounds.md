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
G3 remain open. All four reduction statements are now Proved on Prove2Me.


## Verified Prove2Me central-degree reductions

All four central-degree reductions are private and Proved, with verified
submissions and exact server proof-source readbacks. Both revisions pass
four original types and dependency sets, four definition comparisons,
fourteen original inline helper types and the inline subsetCoinSums value.
All original proof and helper bodies are retained. Four existing Proved
interfaces are reused. The conditional G2 theorem is the supporting root.

The consolidated DAG has 977 nodes and 2249 edges. All 672 proof dependency sets across 29 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The central absolute bounds from degree four onward remain unproved.
These are conditional reductions and do not close generic G2.

* partial_choose_le_repeated_card_add_one_through_three: 561cb87e-2839-4cbd-ba2b-79581fb01b28
* odd_modulus_lower_bound_of_balanced_repeated_bounds: 698c7632-47fc-4854-a0af-678ef218fdf3
* exists_balanced_repeated_bound_failure_of_odd_counterexample: 3aa2e946-098a-4cae-977b-e66c7ddce3af
* oddStratumLowerBound_of_balanced_repeated_bounds: 1971fd39-22d6-4f56-acbb-64fa3209b49f
