# Quartic collision bounds and an explicit sparsity criterion

Let g be a valid tuple of n coordinates. Write R_2(x) for the anchors
of pure quartic representations x=2*g_a+g_i+g_j, where a,i,j are distinct.
Let B=binomial(n,2), and let C be the number of unordered anchor pairs
{a,b} for which

    2*(g_a-g_b)=g_p-g_q

for two distinct coordinates p,q outside {a,b}. The definition
`disjointDoubledDifferencePairs` records precisely these pairs; the
orientation is existential, so each unordered pair is counted once.

Six theorems connect the existing incidence identity to a quantitative
quartic lower bound.

* If a doubled anchor difference has no coordinate representation, at
  most six selected values belong to both anchor fibres. This holds in
  every additive commutative group.
* If the difference is represented by g_p-g_q, injective doubling gives
  at most n-3 common values when both endpoints avoid the anchors, and
  zero otherwise. The proof uses the intersection on the n-2 remaining
  coordinates, rather than the larger unrestricted intersection.
* Consequently, exceptional anchor pairs have cap n-3; all other pairs
  have cap six.
* Summing the exact unordered-pair collision identity gives, for n>=9,

      sum_(x in Y) binomial(|R_2(x)|,2) <= 6*B+(n-9)*C.

  Here Y is any selected value set, and doubling is assumed injective.
* At odd modulus and n>=14, the explicit sparsity hypothesis

      3*(n-9)*C <= 2*(n-14)*B

  implies at least binomial(n,3) quartic repeated values outside the
  doubled two-coin cover. This follows by combining the collision bound
  with the proved incidence supply (n-4)*B and the identity
  3*binomial(n,3)=(n-2)*B.
* Adding the exact doubled two-coin baseline yields

      |D_4| >= binomial(n+1,2)+binomial(n,3).

The sparsity hypothesis is not asserted for arbitrary valid tuples.
Dense exceptional cases remain open. This is a quartic result; the
absolute central inequalities required for generic G2 remain open,
along with G1 and G3.

All six original proofs pass on Lean 4.32 / Mathlib
81a5d257c8e410db227a6665ed08f64fea08e997 and Lean 4.33.1 / Mathlib
0df444a360eaa60ab8c11dca51a86af692955474. Seventeen exact declaration types
and five definition values agree. The compiler axiom audit finds only
standard Lean axioms. Builds reuse cached dependencies and use at most
four compiler threads. Split Prove2Me export and publication remain.
