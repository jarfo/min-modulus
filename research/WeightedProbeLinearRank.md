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
absolute target. G1, G2 and G3 remain open. These four field-version
statements have not yet been exported or uploaded to Prove2Me.
