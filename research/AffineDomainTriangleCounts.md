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
All six results are now verified privately on Prove2Me and integrated
into the consolidated DAG.


## Verified Prove2Me affine-domain count chain

All six affine-domain counting results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify six original target types and dependency sets, five
external interface types, two original inline helper types and three
definition values. Every original proof body is retained. One new
bundle contains the full positive and negative domains. Two supporting
roots retain all six results.

The consolidated DAG has 1145 nodes and 2626 edges. All 761 exact proof dependency sets across 47 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

Large-domain extraction under an explicit missing-pair density hypothesis is verified locally. Absolute central inequalities and generic G1/G2/G3 remain open.

* negative_affine_offsets_eq_of_two_coordinates: 1176b64c-e02e-44c0-8fb3-1fa7cfb9bbbe
* positive_affine_domains_inter_card_le_one: fcc3315c-9e6f-4f10-bcc8-99459b6c3c63
* negative_affine_domains_inter_card_le_one: 5a38a43d-55c3-4bc7-8402-702366191ed1
* cyclic_negative_affine_full_domain_card_le: 3be381a9-0686-4b9e-a6c0-d9e523b9f256
* positive_affine_domain_family_triangle_count_le: 82e2e881-7ca8-4f2e-b08c-ec0e733b7539
* negative_affine_domain_family_triangle_count_le: 6f104839-5417-4052-ae99-e6e85b719342
