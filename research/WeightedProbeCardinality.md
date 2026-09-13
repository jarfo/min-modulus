# A concrete probe-injectivity criterion for repeated-sum cardinality

[WeightedProbeCardinality.lean](WeightedProbeCardinality.lean) defines a
single matrix-weighted combination of the existing anchor/removal probes.
The same matrix must recover every squarefree coefficient vector from
its values outside the doubled half-degree coin cover.

Four theorems are proved:

* Doubling any positive-degree coin value produces a repeated coin value
  of twice the degree.
* Every degree-d probe vanishes outside the repeated degree-(d+1) cover.
* If one weighted probe combination recovers every coefficient in degree
  2k+1, then |C_(k+1)| + choose(n,2k+1) <= |D_(2k+2)| at odd modulus.
  This counting implication does not require validity. Coefficients can
  lie in any finite nontrivial semiring, including finite fields.
* For a valid tuple, the quartic specialization gives
  |D_4| >= choose(n+1,2) + choose(n,3), the required absolute quartic bound.

The proof encodes coefficient vectors by their weighted probe values on
D_(2k+2) minus 2*C_(k+1). Vanishing outside the repeated cover extends
equality of these encodings to every value outside 2*C_(k+1). The assumed
recovery property makes the encoding injective. Counting vectors over a
finite coefficient set gives choose(n,2k+1) <= |D_(2k+2) minus 2*C_(k+1)|.
Injective doubling then restores the baseline |C_(k+1)|.

All four original proof bodies pass both Mathlib revisions with nine
exact printed types, five matching definition values and standard axioms.
The argument is uniform in n and in the even output degree. It performs
no finite search. The build uses selective caches and at most four
compiler threads.

The matrix recovery hypothesis remains unproved. The earlier result that
all probes jointly determine coefficients does not imply that one fixed
matrix combination does so. In degrees above four, the displayed bound
also does not supply all the lower binomial terms in the central absolute
target. Neither this criterion nor the quartic half-fibre bound closes
G1, G2 or G3. All four statements and their weighted-probe definition are now published and verified on Prove2Me.


## Verified Prove2Me weighted-probe implications

All four weighted-probe implications are private and Proved, with
verified submissions and exact server proof-source readbacks. The new
weighted-probe definition is private and verified. Both revisions pass
four exact original types and dependency sets, five definition values
and two original inline helper types. All original proof and helper
bodies are retained. Two existing Proved interfaces are reused. The
conditional quartic result is the terminal supporting root.

The consolidated DAG has 984 nodes and 2263 edges. All 676 proof dependency sets across 30 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The coefficient-recovering matrix remains unproved. In higher degrees,
more lower-binomial terms are needed. These implications do not close G2.

* doubled_coin_cover_subset_repeated_coin_cover: d3d6e0fe-8c9e-4248-ab5c-18c5a52c8ec0
* single_repeat_probe_eq_zero_outside_repeated: 5ab11b5a-8d47-461a-a796-324f0e0ae2b2
* even_degree_card_bound_of_weighted_probe_injective: d52e2c2b-21b4-4956-81b0-304375286f07
* absolute_quartic_bound_of_weighted_probe_injective: a9f2bce0-f79d-436e-ac62-243c4e840920
