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
imports. All six results are now verified on Prove2Me and integrated into the
consolidated DAG.

The global repeated-value count, absolute central inequalities and
G1/G2/G3 remain open. Quartic alone would not settle generic G2.


## Verified Prove2Me incidence chain

All six global incidence results are private and Proved.
Verified submissions and exact server proof-source readbacks pass. Both
revisions verify six original target types and dependency sets, three
external interface types, three inline helper types, one bundled helper
type, four ordinary definition values and the inline configuration
definition value. Every original proof body is retained. Three existing
proved interfaces are reused; no new definition bundle is introduced.
Three supporting roots retain all six results.

The consolidated DAG has 1069 nodes and 2444 edges. All 723 exact proof dependency sets across 38 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The incidence identities and collision reductions are proved. Bounding
the total loss sufficiently for the absolute central inequalities and
generic G1/G2/G3 remains open.

* sum_single_repeat_fibre_card_on_values: c78cb298-9379-4da0-a279-606221310026
* single_repeat_outside_doubled_cover_incidence_lower_bound: 61f15893-5b37-4839-8628-cc6212c34afa
* single_repeat_incidence_le_values_add_pair_collisions: 7efd10ae-fa73-49e1-859b-d1e7109d437b
* single_repeat_outside_doubled_cover_pair_collision_bound: 7837310f-230a-4522-a480-fc5a500ddb2e
* single_repeat_pair_collisions_eq_sum_anchor_pairs: 008c3022-5eff-4448-ab65-5d844404457a
* single_repeat_pair_values_card_le_residual_intersection: 0a6e9432-aeb5-4cc4-9ce6-64e26fe615c1
