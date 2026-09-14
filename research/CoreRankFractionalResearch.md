# Core-rank bounds and fractional certificates

Ten generic lemmas group translation cores by size and combine two
independent cardinality caps with one shared fractional packing bound.
If c_j is the number of size-j cores supported in A, validity gives
c_j<=choose(2*j,j), while injective doubling gives c_j<=choose(|A|,2*j).
The exact match count is sum_j c_j*choose(|A|-2*j,k-j). Nonzero
translations have no empty core, so their ranks begin at one.

The shared rational inequality is sum_j c_j/choose(2*j,j)<=1. Thus
any alpha>=0 and beta_j>=0 with

    choose(|A|-2*j,k-j) <= alpha/choose(2*j,j)+beta_j

give the match-count bound

    |matches| <= alpha + sum_j min(choose(2*j,j),choose(|A|,2*j))*beta_j.

Every sum is over an explicit finite cover of the core ranks. The
certificate hypotheses are explicit; no certificate sufficient for the
central-degree goal is supplied. Unrestricted G1/G2/G3 remain open.
The original proofs are in SquarefreeTranslationCoreRanks.lean and
NonuniformTranslationFractional.lean.

All ten results are private and Proved on Prove2Me. Verified
submissions and exact server proof-source readbacks pass. Both revisions
verify ten original target types and dependency sets, five external
interface types, seven original inline helper types and four existing
definition values. All original proof bodies are retained. No new
definition bundle is needed. Two supporting roots retain the explicit
positive-rank bound and the combined fractional certificate.

The consolidated DAG has 1220 nodes and 2794 edges. All 801 exact proof dependency sets across 53 bundles match. G1/P6, G2/From7 and G3/From7 remain open.

The numerical certificate premises remain explicit. Sufficient central-degree estimates and unrestricted G1/G2/G3 remain open.

* squarefree_translation_core_rank_card_le_choose: 9933b696-b8ee-45be-9fb1-8221a590e4a6
* squarefree_translation_core_rank_card_le_support_choose: b5d413f3-9586-4873-b068-944100bcae3d
* squarefreeTranslationMatches_card_eq_sum_core_ranks: bbc1ceba-48c7-42cf-b60f-1f899f57ac6f
* squarefree_translation_matches_card_le_sum_rank_caps: 0b3ea3fa-297f-4536-a405-48229d0ac856
* squarefree_translation_core_card_pos_of_ne_zero: ee1692d2-bfbe-4f76-ab93-5217de92f66d
* squarefree_translation_matches_card_le_sum_positive_rank_caps: 20f8976c-05dd-4f05-8f87-f4a83b3985dc
* equal_evaluation_disjoint_family_fractional_sum_le: eb993b73-0cb3-41f9-9e07-eed3a83c6c8d
* squarefree_translation_cores_fractional_sum_le: 8d50a0d1-df16-417a-9228-b6d6d591363f
* squarefree_translation_core_ranks_fractional_sum_le: 2ea0768b-90cd-4148-ac5d-55fecd7c7d7b
* squarefree_translation_matches_card_le_rank_dual: 87ab3560-2498-4871-bece-5ad9493c5e98
