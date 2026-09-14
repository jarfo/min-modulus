# Missing incidences and averaged pair deficits

Two purely finite counting lemmas connect the outside-neighbor bounds
to a bound on the size of a domain complement.

* For disjoint finite sets A and S, let R(a) be any family of finite sets.
  If an unordered-pair family D contains {a,i} for every a in A and
  i in S\R(a), then sum_a |S\R(a)|<=|D|. The incidence map is injective:
  disjointness of the two sides prevents an endpoint swap.
* If |A|>=2 and every distinct a,b in A satisfy M<=d(a)+d(b)+C, then
  |A|*M<=2*sum_a d(a)+C*|A|. Summing over each erased diagonal counts
  every deficit twice per pair; positive-factor cancellation finishes.

Both original proofs and both exact declaration types pass the original
and supported Lean/Mathlib revisions with only standard axioms. No
MinModulus definition, group hypothesis or external theorem interface is
needed. The incidence coverage and pairwise inequality are explicit.

The next step is to combine these counts with the full positive domain
neighbor bounds and the missing-pair density hypothesis. The one-escape
conclusion, absolute central inequalities and generic G1/G2/G3 remain
open. Split Prove2Me export and private publication remain.

## Verified Prove2Me dense-case chain

These results are included in the fourteen-theorem dense positive-domain
chain, now private and Proved. See [the consolidated chain](DensePositiveDomainResearch.md).
The density premise is explicit, and unrestricted G1/G2/G3 remain open.
