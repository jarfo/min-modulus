# Nonuniform translation packing and exact core counts

Eight generic lemmas combine nonuniform translated-support packing with
an exact arbitrary-degree count of squarefree translation matches.

For disjoint equal-evaluation pairs with fixed cardinality gap, separating
permutation events are disjoint even when support sizes vary. Natural
weights w satisfying w*choose(|U|+|V|,|U|)<=M therefore have sum at most M.
With injective doubling, a fixed union determines a pair of prescribed
first-side size and signed value; a balanced size-j family supported in A
has at most choose(|A|,2*j) members.

Every degree-k translation match decomposes uniquely into disjoint
differences U,V and a common support H outside their union. Thus

    |matches| = sum_(U,V) in cores choose(|A|-2*|U|,k-|U|).

This identity needs no validity assumption. For valid tuples, any M
bounding choose(|A|-2*j,k-j)*choose(2*j,j) at every core size present
bounds the match count. This numerical premise is explicit; sufficient
central-degree estimates and unrestricted G1/G2/G3 remain open.

The original proofs are in NonuniformTranslatedPacking.lean and
SquarefreeTranslationCoreCount.lean. The new definition bundle contains
the original separating-permutation event definition (previously inline)
and the new squarefreeTranslationCores definition.

All eight results are private and Proved on Prove2Me. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify eight original target types and dependency sets, three external
interface types, eight original inline helper types and four definition
values. All original proof bodies are retained. One new definition bundle
contains the separating-event and disjoint-core definitions. Two supporting
roots retain the support-union cap and the final weighted match bound.

The consolidated DAG has 1200 nodes and 2744 edges. All 791 exact proof dependency sets across 52 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The numerical core-weight premise remains explicit. Sufficient central-degree estimates and unrestricted G1/G2/G3 remain open.

* equal_evaluation_disjoint_family_separating_sum_le: 6c41a64c-682f-480e-9af6-da880f0f8ce4
* equal_evaluation_disjoint_family_weight_sum_le: 12cbb44c-cd48-40e7-b5b0-e4afc77d9947
* equal_evaluation_balanced_pair_eq_of_union_eq: c67b9686-2580-4555-8fce-8b3d494efe37
* equal_evaluation_disjoint_family_card_le_support_choose: 6723eb45-4a58-41c7-8f8f-87c4a5cc9d60
* mem_squarefreeTranslationCores: 4e08f717-7751-49e1-b363-dd74b149b1c2
* squarefree_translation_match_core_data: f23db6ba-7b77-46b8-a14c-da0cf935eda6
* squarefreeTranslationMatches_card_eq_sum_cores: 39858667-769b-40ee-b5c4-eafea0163022
* squarefree_translation_matches_card_le_weight_bound: 142fa4bd-c8bb-424d-aa53-c1ae8c987c5c
