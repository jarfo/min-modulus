# Arithmetic for a dense positive-domain complement

Three scalar implications hold for all natural-number parameters at
n>=144; there is no finite search or enumeration.

* The density bound (n-9)*D<3*choose(n,2) implies 5*D<8*n.
* Suppose M+r=n and n<2*M+40. If r>=2 implies r*M<=2*D+6*r,
  the same density bound forces r<=12.
* If M+r=n, r<=12 and r*M<=D+13*r, that density bound forces r<=1.

The first proof uses the binomial identity 2*choose(n,2)=n*(n-1).
The second combines the large-domain inequality with the averaged pair
bound. The last uses the total missing-incidence bound after every
outside coordinate has at most thirteen represented neighbors.

All three original proofs and exact types pass both installed
Lean/Mathlib revisions with only standard axioms. No new definitions or
group hypotheses occur. The scalar premises are explicit; connecting
them to a full affine domain is a separate theorem under development.

These results do not infer the density premise from a small modulus.
Absolute central inequalities and generic G1/G2/G3 remain open.
Split Prove2Me export and private publication remain.
