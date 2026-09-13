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
G1, G2 or G3. These four statements and their weighted-probe definition
await platform export and upload.

## Verified four-theorem weighted-probe export

All four weighted-probe results have a verified split export with one
new definition bundle for the weighted combination. Both revisions pass
four exact original types and dependency sets, five definition type/value
comparisons and two original inline helper types. All original theorem
and helper bodies are retained. Two existing Proved theorem interfaces
are reused. The conditional quartic bound is the terminal root and
retains the general even-degree implication and both support lemmas.
Metadata, exact live dependencies and unused names pass. The new
definition and four nodes have not yet been uploaded. Matrix existence,
the missing higher-degree binomial terms, and G1/G2/G3 remain open.
