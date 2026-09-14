# Triangle counts in full affine domains

For a tuple g, the full positive domain at offset t consists of coordinates
i with g(j)+t=2*g(i) for some coordinate j. The full negative domain consists
of i with g(j)+2*g(i)=t. These are the two definitions in this module.

The six proved results connect the generic block-family count to
the represented-triangle classification.

* Two negative affine offsets that both map two distinct coordinates into
  a valid tuple are equal when doubling is injective.
* Distinct positive offsets, and distinct negative offsets, therefore give
  full domains meeting in at most one coordinate.
* For a valid cyclic tuple with injective doubling, a full negative domain
  has at most floor((n+2)/2) coordinates. The proof chooses a partial affine
  map from the domain witnesses and applies the existing cyclic bound.
* For a finite offset set F and a bound M on its positive domain sizes,

      3*sum_{S in image(domain+,F)} choose(|S|,3)
        <= (M-2)*choose(n,2).

* For a finite set of negative offsets in a nonzero cyclic modulus,

      6*sum_{S in image(domain-,F)} choose(|S|,3)
        <= (n-2)*choose(n,2).

The sums range over distinct full domains. Empty and small domains are
included, and subtraction is natural-number subtraction. Positive results
hold in every additive commutative group with injective doubling; negative
cardinality and final counting use the nonzero cyclic modulus explicitly.

Represented triangles still have to be assembled into the affine families
and the exceptional L-shape family. That total triangle count, extraction
of a large positive domain, the absolute central inequalities and generic
G1/G2/G3 remain open.

All six original proofs pass both Mathlib revisions. Sixteen exact
declaration types and three definition values agree: ValidTuple and the
two new affine-domain definitions. Only standard Lean axioms occur.
Split Prove2Me export and publication remain.

## Verified six-theorem affine-domain count export

All six statements and original proof bodies have a verified split
export on both revisions. Six exact target types and dependency sets,
five external interface types, two original inline helper types and
three definition values agree. One new bundle contains the full
positive and negative affine-domain definitions. Metadata and live
preflight pass; publication is pending. The validity, doubling and
domain-size hypotheses remain explicit. Large-domain extraction,
absolute central inequalities and generic G1/G2/G3 remain open.
