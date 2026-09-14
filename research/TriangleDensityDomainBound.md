# A large positive affine domain from few missing pairs

Let g be a valid tuple at a nonzero cyclic modulus with injective
doubling. Let D be a family of two-element coordinate subsets covering
every pair whose doubled difference has no coordinate-difference
representation. D may also contain represented pairs.

Three results connect the triangle counts to an actual large domain.

1. If n>=2, M>=2, and every full positive affine domain has size at most M,

       n*binomial(n,2)
         <= (2*M+4)*binomial(n,2)+6*(n-2)*|D|.

   Use all represented triangles as Ts. The missing-pair lower bound and
   total represented-triangle upper bound give this inequality.
2. If n>=16 and the explicit density condition

       (n-9)*|D| < 3*binomial(n,2)

   holds, any such M satisfies n<2*M+40.
3. If n>=44 under the same density condition, there is an actual offset t
   with

       n < 2*|positiveAffineDomain g t|+40.

   Maximize the domain size over the finite cyclic group. The numerical
   bound rules out a maximum below two and yields an attained large domain.

All three original proofs pass both Mathlib revisions. Eight exact
declaration types and three existing definition values agree, with only
standard Lean axioms. No new definition is introduced. Split Prove2Me
export and publication remain.

The missing-pair density and dimension thresholds are explicit. This
extracts a domain of roughly half the coordinates, not one-escape closure.
Next combine its outside-neighbor restrictions with the same missing-pair
budget. The density premise has not been deduced merely from a small
modulus; it is suggested by failure of the quartic count. Higher central
degrees and generic G1/G2/G3 remain open.
