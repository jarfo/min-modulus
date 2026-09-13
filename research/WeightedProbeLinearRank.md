# Weighted-probe rank over an arbitrary field

[WeightedProbeLinearRank.lean](WeightedProbeLinearRank.lean) removes the
finite-coefficient assumption from the weighted-probe cardinality
criterion when coefficients lie in a field. This permits a future proof
to use a rational-function field containing symbolic matrix entries,
without first specializing the matrix to a finite field.

Four results are proved:

* Weighted probes preserve addition of coefficient vectors over any
  semiring.
* Over a commutative semiring, probes commute with scalar multiplication.
* Over any field K, a fixed coefficient-recovering weighted probe outside
  2*C_(k+1) implies |C_(k+1)| + choose(n,2k+1) <= |D_(2k+2)| at odd
  modulus. This implication needs no validity assumption.
* For a valid tuple, the quartic specialization gives
  |D4| >= choose(n+1,2)+choose(n,3).

The proof constructs a linear map from coefficient vectors indexed by
squarefree supports to values indexed by D_(2k+2) minus 2*C_(k+1).
The assumed coefficient recovery makes this map injective. Finite
vector-space dimension, rather than the number of field elements,
bounds the number of support coordinates by the number of output values.
The existing doubled-cover containment and injective doubling restore
|C_(k+1)|. The support and output sets are finite even when K is infinite.

All four original proof bodies pass Lean 4.32 and Lean 4.33.1 against the
original and supported Mathlib revisions. Nine exact printed declaration
types, five definition values, and standard-axiom audits match. The build
uses selective caches and at most four compiler threads. No new
definition or finite search is introduced.

A coefficient-recovering matrix is still unproved. In particular, the
joint injectivity of all separate probes does not establish injectivity
of a single weighted combination. For degrees above four, the displayed
bound also lacks some lower binomial terms required by the central
absolute target. G1, G2 and G3 remain open. All four field-version statements are now Proved on Prove2Me.


## Verified Prove2Me field-linear weighted-probe results

All four field-linear probe results are private and Proved, with verified
submissions and exact server proof-source readbacks. Both revisions pass
four original types and dependency sets, five definition comparisons
and two original inline helper types. All original theorem and helper
bodies are retained. Four Proved interfaces are reused, with no new
definition. The conditional quartic bound over any field is the root.

The consolidated DAG has 990 nodes and 2278 edges. All 680 proof dependency sets across 31 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The recovering matrix and missing higher-degree binomial terms remain unproved.
These are conditional rank implications and do not close generic G2.

* weighted_single_repeat_probe_add: 4ab6a46e-e7b8-438c-a7e8-01a10ddc9f6a
* weighted_single_repeat_probe_smul: 273ec338-6474-4db3-82be-1d6069d14357
* even_degree_card_bound_of_weighted_probe_injective_field: d58ea37f-5143-4c3b-ae8a-64f259391f9e
* absolute_quartic_bound_of_weighted_probe_injective_field: 67406726-99c1-4844-bac4-aa337924b21f
