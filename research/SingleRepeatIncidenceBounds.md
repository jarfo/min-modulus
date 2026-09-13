# Global single-repeat incidences and collision losses

Let g be a valid tuple, and let R_k(x) be the anchors of its pure
single-repeat representations of degree k+2. Six Lean results connect
these fibres to the translated-intersection bounds.

For any selected value set Y, the first theorem gives the exact identity

    sum_(x in Y) |R_k(x)|
      = sum_(S squarefree, |S|=k)
          #{a outside S : 2*g_a+sum(S) belongs to Y}.

The proof reindexes existing single-repeat configurations by their
residual support and anchor. The projection to fibre anchors is already
known to be bijective under validity, so no multiplicity is lost.

At odd modulus, set E=2*C_(k+1), where C_d is the exact d-coin cover.
Summing the existing midpoint escape bound over all 2k-element supports
then gives

    (n-(2k+2))*binomial(n,2k)
      <= sum_(x outside E) |R_(2k)(x)|,   k>=1.

Natural-number subtraction is truncated at zero. The elementary
inequality r<=1+binomial(r,2), together with membership of every occupied
fibre in the repeated cover D_(2k+2), yields

    (n-(2k+2))*binomial(n,2k)
      <= |D_(2k+2) without E|
         + sum_(x outside E) binomial(|R_(2k)(x)|,2).

The pair-collision sum is exactly the sum over unordered anchor pairs P
of the number of selected values whose fibre contains P. This reindexing
holds in every additive commutative group without a validity assumption.
Finally, common values of distinct anchors a,b inject into the translated
intersection of k-element squarefree sums on coordinates excluding a,b,
with shift 2*(g_a-g_b). This last bridge uses validity but not oddness.

At quartic degree, the incidence supply is (n-4)*binomial(n,2). The proved
six-point bound away from coordinate differences and the restricted
coordinate-difference bounds can now be applied to each anchor pair.
Bounding their total contribution, including dense exceptional cases,
remains unfinished. No upper bound on that total loss is asserted here.

All six original proof bodies pass both Mathlib revisions. Sixteen exact
types and five definition values agree; only standard Lean axioms occur.
There are no new definitions, finite enumeration jobs or default-library
imports. Prove2Me export and publication remain.

The global repeated-value count, absolute central inequalities and
G1/G2/G3 remain open. Quartic alone would not settle generic G2.

## Verified six-theorem incidence export

All six incidence statements and original proof bodies have a verified
split export on both revisions. Exact target types, three external
interfaces, three inline helper types, one bundled helper type and six
dependency sets agree. Four ordinary definition values and the inline
configuration definition value agree. No new definition bundle is
introduced. Metadata and live preflight pass; publication is pending.
The exact global collision sum is now reduced to translated residual
intersections. Absolute central counts and generic G1/G2/G3 remain open.
