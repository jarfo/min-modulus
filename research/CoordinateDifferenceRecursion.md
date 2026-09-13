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
open. Prove2Me split export and upload are the next verification stage.

## Verified ten-theorem recurrence export

All ten recurrence statements and their original proof bodies have a
verified split export on both revisions. Exact target types and dependency
sets agree, as do the two reused interface types and two definition
values. The export adds one lightweight definition bundle and reuses two
private Proved theorem interfaces. Metadata and live preflight pass.
Publication is pending. The doubled-shift remainder still needs control;
absolute central bounds and generic G1/G2/G3 remain open.
