# Exact all-degree coordinate-difference recurrence

For a valid tuple g in any additive commutative group, write S_d(A) for
the values of sums over d distinct allowed coordinates, and set

    I_d(A,t) = |(S_d(A)+t) intersect S_d(A)|.

For distinct p,q in A, the Lean proof establishes the exact identity

    I_(k+1)(A,g_p-g_q)
      = binomial(|A|-2,k) + I_k(A without {p,q},2*(g_p-g_q)).

If either p or q is absent from A, the intersection is empty in every
degree. No injectivity of doubling or odd-order hypothesis is needed.
The formula includes k=0 and degrees larger than the allowed set.

The proof classifies support matches sum(S)+g_p=sum(T)+g_q.

* If p is absent from S, validity forces S=insert q H and T=insert p H,
  where H is a k-element support outside both endpoints. These are
  exactly binomial(|A|-2,k) matches.
* If p belongs to S, validity forces q in T, q outside S and p outside T.
  Erasing p and q gives equal-degree k-supports outside both endpoints
  whose sums differ by twice the original shift. Inserting the endpoints
  is the inverse, so this is an exact bijection.
* Equal-cardinality squarefree sums uniquely determine their supports
  by validity. Thus projecting a support match to its common value is
  bijective, and support counts equal value-intersection counts.

The source contains ten theorems and one noncomputable finite-set
encoding of support matches. Both the original and supported Mathlib
revisions verify all original proof bodies. The audit compares fourteen
exact declaration types, including both reused theorem interfaces, and
the values of ValidTuple and squarefreeTranslationMatches. Only standard
Lean axioms occur. No finite enumeration is used.

Deleting two coordinates and lowering the degree by one preserves the
central-degree relation. The residual shift need not be a coordinate
difference on the remaining coordinates, so the identity alone does not
close an induction. The next task is to bound that residual intersection
using validity and the relation that produced the doubled shift. The
absolute central repeated-sum inequalities and generic G1/G2/G3 remain
open. All ten results and the supporting definition are now verified on Prove2Me.


## Verified Prove2Me recurrence chain

All ten all-degree recurrence results are private and Proved. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify ten original target types and dependency sets, two reused
interface types and two definition values. Every original proof body is
retained. Two existing proved interfaces and one lightweight definition
bundle are used. Two supporting roots retain the complete recurrence and
all-degree endpoint exclusion.

The consolidated DAG has 1051 nodes and 2405 edges. All 713 exact proof dependency sets across 36 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The exact recurrence is proved. Its residual doubled shift need not be a
coordinate difference on the remaining coordinates. Controlling this
remainder and proving the absolute central bounds remain open, as do
generic G1/G2/G3.

* coordinate_difference_match_normal_form: 227a1463-35d6-4ecc-8d67-7c781143fddd
* coordinate_difference_match_repeated_form: 9332b28a-4d5d-46b3-8d68-efb7dd019312
* coordinate_difference_match_endpoints_mem_any_degree: 7a26e873-5ed0-4fb5-a432-87415d5a4690
* coordinate_difference_intersection_eq_empty_of_endpoint_missing: d9e38a38-6c27-4aa1-b906-69c158c532c6
* mem_squarefreeTranslationMatches: 7b946a9e-e523-493f-b741-5b0c1ecd345d
* squarefreeTranslationMatches_card_eq_intersection: 4d1c5dc4-5ef6-4d0c-a710-57dcbf714303
* coordinate_difference_normal_matches_card: f449ace4-5785-4abf-89b8-cdf70c0e4533
* coordinate_difference_repeated_matches_card: 791b11fb-6deb-4477-bc25-0730d6699e15
* coordinate_difference_matches_card_recursion: 504a2a8f-1ff3-4534-a5dd-2c59cffec79a
* coordinate_difference_intersection_card_recursion: 978f2198-a424-4b6f-a764-d0e4e97c2fad
