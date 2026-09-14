# Dense positive-domain proof chain

For a valid tuple of length n>=144 at odd modulus N, let D be a family
of two-coordinate subsets covering every unrepresented doubled coordinate
difference. If (n-9)*|D|<3*choose(n,2), then 2^n-1<=N. The density
premise is explicit. The proof obtains a large full positive affine
domain, bounds its complement by one, and applies AlmostDoubling.

Any remaining odd counterexample at n>=144 must satisfy
3*choose(n,2)<=(n-9)*|D| for every such pair cover. This argument does
not cover n<144; existing small-dimension results remain valid. The sparse
represented-pair regime, absolute central inequalities and unrestricted
G1/G2/G3 remain open.

The fourteen original proofs are in five source modules:

* FullPositiveDomainNeighbors.lean: four domain-map and neighbor bounds.
* CrossPairDeficit.lean: two incidence and averaging bounds.
* DenseDomainComplementArithmetic.lean: three scalar density implications.
* DensePositiveDomainOneEscape.lean: three actual one-escape extraction results.
* DensePairModulusBound.lean: the sharp odd bound and necessary counterexample density.

All fourteen results are private and Proved on Prove2Me. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify fourteen original target types and dependency sets, four external
interface types, one original inline helper type and two existing
definition values. All original proof bodies are retained. No new
definition bundle is required. One terminal root retains all fourteen
results, including the conditional sharp odd bound and its necessary
counterexample-density consequence.

The consolidated DAG has 1184 nodes and 2709 edges. All 783 exact proof dependency sets across 51 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The density premise remains explicit. The sparse represented-pair regime, absolute central inequalities and unrestricted G1/G2/G3 remain open.

* full_positive_affine_domain_map_exists: c826d530-dee8-4570-9a8c-d275c08be131
* full_positive_affine_outside_neighbors_card_bound: b49770e2-6cb8-4837-925f-06092558163c
* full_positive_affine_outside_rich_intersection_card_le_one: 011d3023-0c03-4eca-afdf-6201e7caeabe
* full_positive_affine_outside_pair_missing_bound: ba5b175c-0250-467a-b814-b41a9cd3f557
* cross_missing_incidence_sum_le_pair_family: 13ad1f76-1bbb-4073-926d-45595890a497
* pair_deficit_average_bound: d13418fc-bb2e-451e-b1fc-dc3e8181ca0e
* few_missing_pairs_linear_bound: fb2e5e33-e9e6-4f44-bd3b-14da8a7c8bd4
* dense_domain_averaged_complement_le_twelve: 476acd0d-e46f-4368-84f1-4eeca8f880f2
* dense_domain_bounded_neighbors_complement_le_one: bb67a2ec-f1b5-424b-b944-7b52e40c87a2
* full_positive_affine_domain_complement_le_one_of_few_missing_pairs: bf8b563e-a7ec-4785-9b14-041ecfcffc64
* exists_positive_affine_domain_complement_le_one_of_few_missing_pairs: a4767fbc-c94d-4f8e-8bd7-84081eae9a0d
* exists_one_escape_doubling_of_few_missing_pairs: 4bc87b73-caa9-4a67-b994-98d9f1956229
* odd_lower_bound_of_valid_few_missing_pairs: f77d5805-d66c-4018-b532-f96b04570b17
* pair_cover_density_of_valid_odd_modulus_counterexample: d8768155-950d-488e-bc03-09a933eb11c1
