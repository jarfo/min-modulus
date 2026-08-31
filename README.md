# Minimum modulus for the unique multiset-sum problem

[![Lean CI](https://github.com/jarfo/min-modulus/actions/workflows/build.yml/badge.svg)](https://github.com/jarfo/min-modulus/actions/workflows/build.yml)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)

This repository is the Lean 4 formalization accompanying the paper

> José A. R. Fonollosa, *Minimum modulus for the unique multiset-sum problem*,
> [arXiv:2607.08366](https://arxiv.org/abs/2607.08366), 2026.

The code in this repository is licensed under the Apache License 2.0; see [LICENSE](LICENSE).

The main theorem of the paper is kernel-checked end-to-end: `nmin_eq` builds
with **0 errors, 0 sorries** and uses only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`, checked with `#print axioms nmin_eq`).

The repository also formalizes Proposition 2 of the paper (optimality among
elementary abelian $`2`$-groups): if $`g_0, \dots, g_{n-1} \in (\mathbb{Z}_2)^k`$
have unique multiset sums, then $`k \ge n - 1`$, so the least such group has
order $`2^{n-1}`$. See [Proposition 2](#proposition-2-elementary-abelian-2-groups)
below (also 0 sorries, standard axioms only).

Finally, the repository formalizes the resolution of **open problem 4** of the
paper — the exact minimum order for unique multiset sums over *all* finite
abelian groups — following

> Michael Inal, *The Exact Minimum Order for Unique Multiset Sums in Finite
> Abelian Groups*, [OSF preprint](https://doi.org/10.17605/OSF.IO/C58Q9), 2026.

The answer is $`m_{\mathrm{ab}}(n) = 2^{n-1}`$: a lower bound valid over every
finite abelian group (not just elementary abelian ones), matched by the
elementary abelian construction, with a classification of the extremal case.
See [Open problem 4](#open-problem-4-all-finite-abelian-groups) below (0
sorries, standard axioms only).

## The problem and the theorem

Fix $`n \ge 2`$. A set $`A = \{a_0 < \dots < a_{n-1}\}`$ of residues in
$`\mathbb{Z}_N`$ is **valid mod $`N`$** if the all-ones multiset is the *only*
size-$`n`$ multiset drawn from $`A`$ whose sum is $`p = \sum a_i \pmod N`$.
Validity is exactly the condition under which the permanent of an
$`n \times n`$ matrix equals a single coefficient of its row-product
polynomial mod $`x^N - 1`$, extractable by a size-$`N`$ transform (a DFT over
$`\mathbb{C}`$, or a number-theoretic transform over a finite field) — so one
wants the smallest modulus $`N`$ that is still valid.

For the super-increasing set $`A = \{2^k - 1 : 0 \le k < n\}`$ the paper proves

> **Theorem.** $`N_{\min}(n) = 2^n - 2^{\lfloor \log_2 n \rfloor}`$ for all $`n \ge 2`$.

The Lean development proves exactly this, for all $`n \ge 2`$ (not up to a
bound): the main theorem `nmin_eq` states
`IsLeast {N | 2 ≤ N ∧ Valid n N} (2^n − 2^m)` with `m = Nat.log 2 n`, combining
the paper's Theorem A (validity / upper bound) and Theorem B (lower bound).
That this $`N`$ is minimal over *all* residue sets (not just the
super-increasing one) remains a conjecture (Conjecture 1 in the paper,
CP-certified for $`n \le 7`$) and is not proved here; the formalized partial
results and remaining G1/G2/G3 interfaces are summarized below.

## Layout

A single Lake package rooted at the repository root:

```
lakefile.toml, lean-toolchain, lake-manifest.json
MinModulus.lean                 -- root module, imports the files below
MinModulus/
  UniqueSums.lean               -- Theorems A, B and the main theorem `nmin_eq`
  ElemAbelian2.lean             -- Proposition 2 (elementary abelian 2-groups)
  AbelianMin.lean               -- Open problem 4 (all finite abelian groups)
  Descent.lean                  -- two-adic halving/deletion lemmas toward Conjecture 1
  G1Triangle.lean               -- three-witness closure and triangle common-touch family
  G1ThreeDescent.lean           -- delete two coordinates at an order-three difference
  OddOrder.lean                 -- odd-order bound, chain rigidity, linear wedge
  RelationCertificate.lean      -- adjugate/determinant bridge for relation systems
  QuadraticWedge.lean           -- SHC bridge and quadratic/multi-level lemmas
  SubtupleRigidity.lean         -- conditional odd-window subtuple spanning
  SHCBaseCases.lean             -- kernel-checked 3-coordinate SHC bound
  SHCFourBaseCases.lean         -- normalized 4-coordinate window exclusions
  SHCFourGenerator.lean         -- generator coordinates and 4-coordinate SHC bound
  SHCFiveGeneratorReduction.lean -- structural 5-coordinate generator reduction
  SHCFiveGenerator.lean         -- unconditional 5-coordinate window generator theorem
  SHCFiveCertificate.lean       -- trusted bridge for normalized 5-coordinate certificates
  Generated/SHCFiveN*.lean      -- sharded normalized 5-coordinate kernel checks
  SHCFiveBaseCases.lean         -- 5-coordinate SHC bound 63 and odd `n=6` stratum
  SHCSixGeneratorReduction.lean -- structural 6-coordinate generator reduction
  SHCSixGenerator.lean          -- tight 2-prime generator cases
  SHCSixExceptionalCertificate.lean -- trusted order-105 certificate bridge
  Generated/SHCSixN105*.lean   -- sharded order-105 kernel checks
  SHCSixGeneratorComplete.lean  -- full 6-coordinate window generator theorem
  SHCSixCertificate.lean        -- trusted bridge for normalized 6-coordinate certificates
  SHCCardinality.lean           -- uniform cube-plus-translated-layers bounds
  SHCSixCardinality.lean        -- isolated analytic normalized exclusion below 76
  Generated/SHCSixNormalizedN*.lean -- sharded normalized 6-coordinate checks
  SHCSixBaseCases.lean          -- analytic normalized 6-coordinate exclusions through 75
  GlobalRoadmap.lean            -- precise G1/G2/G3 interfaces and G1 dichotomy
scripts/check_axioms.lean       -- axiom audit, run in CI
scripts/generate-five-normalized-certificates.py -- deterministic Torch certificate generator
scripts/generate-six-exceptional-certificate.py -- deterministic order-105 generator
scripts/generate-six-normalized-certificates.py -- deterministic normalized 6-coordinate generator
```

## Build

| | |
|---|---|
| Toolchain | Lean 4 `v4.32.0`, Mathlib pinned `v4.32.0` (prebuilt cache) |
| Build | `lake build` — green (0 errors, 0 warnings, 0 sorries) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only |

With [elan](https://github.com/leanprover/elan) on your `PATH` (it reads
`lean-toolchain` and fetches Lean `v4.32.0` automatically):

```sh
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build
```

To reproduce the axiom audit:

```sh
lake env lean scripts/check_axioms.lean
```

## What is formalized

The development is stated in **`k`-space over ℕ**: a candidate multiset is
`k : ℕ → ℕ` with `∑_{i<n} k i = n`, validity is the paper's k-vector condition
with `Nat.ModEq`, and the paper's signed multiples $`V = \pm jN`$ appear only
through the congruence `M ≡ 2^n − 1 [MOD N]` on $`M = \sum k_i 2^i`$ — no
integer subtraction anywhere.

| Lean declaration | Corresponds to (paper) | Status |
|---|---|---|
| `a`, `dsum`, `val`, `Supp`, `Valid` | Problem statement, k-vector form | ✅ defined |
| `sum_two_pow`, `sum_a_add_dsum` | §3 reduction identities | ✅ proved |
| `not_valid_of_witness` | Lemma 1 (reduction), witness direction | ✅ proved |
| `val_pad`, `dsum_pad`, `supp_mono`, `update_top`, `shift_*`, `unshift_*` | (plumbing) | ✅ proved |
| `ones_rep`, `ones_erase_rep`, `exists_rep_le`, `exists_rep_lt`, `exists_rep_compl` | §6 Prop. 1 (master achievability criterion), existence half | ✅ proved |
| `dsum_succ_of_lt`, `exists_dsum_eq` | Lemma 3 (digit sum), contiguity (upward) half | ✅ proved |
| **`theoremB`** | **§6 Theorem B — lower bound, all four cases** | ✅ **proved** |
| `gmin`, `gmin_add_le`, `gmin_add_pow`, `gmin_ones` | §4 greedy digit sum $`s_{\min}`$, top-coin / all-ones values | ✅ proved |
| `gmin_le_dsum` | Lemma 3 (digit sum), minimality (downward) half | ✅ proved |
| `ones_unique` | Lemma 2 ($`V \ne 0`$) | ✅ proved |
| `dsum_le_val`, `val_le_dsum_mul` | §3 trivial range $`n \le M \le n \cdot 2^{n-1}`$ | ✅ proved |
| `gmin_step` | §5 Lemma 4 (step), $`s_{\min}(M + 2^n - 2^t) \ge s_{\min}(M) + 1`$ | ✅ proved |
| `slack` | §5 slack bound $`s_{\min}(M_j) \ge n + j`$, induction on $`j`$ | ✅ proved |
| **`theoremA`** | **§5 Theorem A — upper bound / validity** | ✅ **proved** |
| **`nmin_eq`** | **Main theorem, `IsLeast {N ∣ 2 ≤ N ∧ Valid n N} (2^n − 2^m)`** | ✅ **proved** |

## Proposition 2: elementary abelian 2-groups

[`MinModulus/ElemAbelian2.lean`](MinModulus/ElemAbelian2.lean) formalizes
Proposition 2: if $`g_0, \dots, g_{n-1} \in (\mathbb{Z}_2)^k`$ have unique
multiset sums, then $`k \ge n - 1`$. Equivalently, the least elementary abelian
$`2`$-group admitting such a family has order $`2^{n-1}`$.

The theorem `MinModulus.elementaryAbelianTwoGroups_optimal` matches the paper's
statement: `UniqueMultisetSums` quantifies over multiplicity vectors
$`m : \mathrm{Fin}\ n \to \mathbb{N}`$ with $`\sum_i m_i = n`$, and casting
$`m_i`$ into $`\mathbb{Z}_2`$ before scaling gives the correct multiset sum in
$`(\mathbb{Z}_2)^k`$. The conclusion `n - 1 ≤ k` (truncated subtraction) is
equivalent to $`k \ge n - 1`$.

The proof follows the paper's argument: the map $`\Lambda(x) = \sum_i x_i g_i`$
and the coordinate-sum functional are built as linear maps; a nonzero
$`u \in \ker \Lambda \cap \ker(\mathrm{sum})`$ has even positive support $`S`$,
and doubling half of $`S`$ while dropping the other half yields a size-$`n`$
multiset with the same group sum but a multiplicity $`\ne 1`$, contradicting
uniqueness; rank–nullity then gives
$`n = \mathrm{rank}\ \Lambda + \dim \ker \Lambda \le k + 1`$.

The hypothesis is non-vacuous: $`n = 2`$, $`k = 1`$, $`g = (0, 1)`$ satisfies it
and meets the bound with equality.

## Open problem 4: all finite abelian groups

[`MinModulus/AbelianMin.lean`](MinModulus/AbelianMin.lean) formalizes Inal's
resolution of the paper's fourth open problem. Write $`n = m + 1`$. A tuple
`g : Fin (m+1) → G` in a finite abelian group `G` is **valid** (`ValidTuple`) if
the all-ones vector is the only $`k : \mathrm{Fin}\ (m+1) \to \mathbb{N}`$ with
$`\sum_i k_i = m + 1`$ and $`\sum_i k_i \cdot g_i = \sum_i g_i`$. Let
$`m_{\mathrm{ab}}(n)`$ be the least order of a finite abelian group admitting a
valid tuple. Then $`m_{\mathrm{ab}}(n) = 2^{n-1}`$.

The key observation is that validity forces the translated differences
$`g_{j+1} - g_0`$ to be **dissociated**: their subset-sum map
`ssum g : Finset (Fin m) → G` is injective (`ssum_injective`), which embeds the
Boolean cube into `G`.

| Lean declaration | Corresponds to (Inal) | Status |
|---|---|---|
| `ValidTuple`, `diff`, `ssum` | Definitions (validity, differences, subset-sum map) | ✅ defined |
| `not_collision_disjoint`, `ssum_injective` | Lemma 3.1 — validity forces dissociation | ✅ proved |
| **`card_ge`** | **Cor. 3.2 — lower bound `2^(n-1) ≤ |G|`** | ✅ **proved** |
| `elem_valid`, `elem_card` | Prop. 3.3 — sharpness (standard tuple in $`(\mathbb{Z}_2)^{n-1}`$) | ✅ proved |
| **`mab_isLeast`** | **Thm. 1.1 — `m_ab(n) = 2^(n-1)`, as `IsLeast`** | ✅ **proved** |
| `diff_order_two`, `equality_order_two`, `ssum_bijective` | Thm. 4.1 — the extremal group is elementary abelian | ✅ proved |
| **`equality_classification`** | **Thm. 4.1 — differences form an $`\mathbb{F}_2`$-basis** | ✅ **proved** |
| **`equality_addEquiv`** | **Thm. 1.1 — explicit $`\phi : G \to (\mathbb{Z}_2)^{n-1}`$, $`\phi(g_i - g_0) = e_i`$** | ✅ **proved** |

The lower bound `card_ge` holds for *every* finite abelian group, strengthening
Proposition 2 (which is restricted to elementary abelian $`2`$-groups) and the
previously available counting bound $`\binom{2n}{n}/2^n`$. At equality, a second
use of validity (representing $`2(g_i - g_0)`$ as a subset sum and rivalling the
all-ones vector with a multiplicity-3 entry) shows every difference has order
two; combined with the bijectivity of `ssum`, the differences form an
$`\mathbb{F}_2`$-basis, so — up to translation and isomorphism — the only
extremal tuple is $`(0, e_1, \dots, e_{n-1})`$ in $`(\mathbb{Z}_2)^{n-1}`$.

This settles the abelian minimum-order question (open problem 4). It is separate
from Conjecture 1 (minimality of $`N`$ over all residue sets in $`\mathbb{Z}_N`$),
which remains open.

## Progress toward Conjecture 1

The `descent` branch also formalizes the current proof program for global
cyclic optimality.  These results do **not** prove Conjecture 1, but they make
its remaining inputs explicit and kernel-check the reusable parts:

| File / declaration | Result |
|---|---|
| `Descent.lean`: `witness_combination`, `deletion_descent`, `pair_descent` | halving and deletion at the order-two element |
| `common_touched_of_unique_omission` | G1 holds when one half-witness has a unique omitted coordinate |
| `three_witnesses_sum_ne_zero` | excludes the exact minimal cyclic three-witness pattern in G1 |
| `G1Triangle.lean`: `witness_three_sum`, `common_touched_of_three_sum_unique_omission` | the sum of three half-witnesses is another half-witness whenever its coefficients remain at least `-1`; a unique omission in that sum forces a G1 common-touch coordinate |
| `common_touched_of_triangle_one_light_opposite` | closes every exact omission triangle whose opposite coefficients, up to permutation, are `1, ≥2, ≥2`; the summed witness has one omission |
| `witness_compl_sum_eq_card_exactOmissions`, `witness_coeff_eq_zero_or_one_or_two_of_exact_pair` | exact omission set `S` leaves precisely `|S|` positive coefficient mass outside `S`; in particular every non-omitted coefficient of a two-omission witness is `0`, `1`, or `2` |
| `triangle_opposite_coefficients_zero_one_or_two`, `not_triangle_all_opposites_two` | reduces exact triangle opposite profiles to `{0,1,2}³` and excludes `(2,2,2)` because each `2` exhausts its witness's positive mass, forcing the three vectors to sum to zero |
| `triangle_one_one_two_sum_witness_zero_opposite` | reduces the residual positive profile `(1,1,2)` to a new witness on the heavy omission edge with opposite coefficient `0` |
| `exists_pair_difference_witness`, `validTuple_injective`, `common_touched_of_pair_difference` | turns a coordinate difference equal to the half element into an exact one-omission witness and hence a G1 common-touch coordinate; validity in particular makes tuple coordinates distinct |
| `common_touched_of_same_exact_pair_zero_two` | closes a same-edge zero/`2` pair in every group with a unique nonzero involution: validity forces the zero witness to concentrate at another coordinate, equality after doubling yields the involution difference, and the pair bridge closes G1 |
| `zmod_eq_zero_or_half_of_add_self_eq_zero`, `common_touched_of_triangle_one_one_two_zmod` | specializes unique involution to `ZMod (2*M)` and closes the exact cyclic triangle profile `(1,1,2)` outright |
| `triangle_all_one_sum_witness_exact_triple` | reduces the residual profile `(1,1,1)` to a witness whose exact omission set is the three triangle vertices |
| `exists_companion_one_of_exact_pair_coeff_one`, `witness_neg_of_le_one` | exposes the hidden companion coordinate of every light two-omission witness and proves that any witness in the symmetric coefficient window `[-1,1]` remains a half-witness after negation |
| `common_touched_of_triangle_all_one_zmod` | closes the cyclic `(1,1,1)` profile: repeated companion coordinates yield equal doubles and a half-modulus difference, while three distinct companions make the exact-triple witness negatable and contradict validity |
| `common_touched_of_triangle_positive_zmod` | combines the `{0,1,2}` classification with the profile theorems to close every strictly positive exact omission triangle in an even cyclic group |
| `common_touched_of_two_adjacent_light_opposites_zmod` | closes any exact cyclic triangle with two adjacent opposite coefficients equal to `1`, including the zero-containing profile `(0,1,1)` up to rotation |
| `exists_pure_companion_two_of_triangle_zero_opposite`, `two_smul_eq_target_add_pair_of_exact_pair_coeff_two` | proves that a zero-opposite edge must be the pure vector `-p-q+2e`, with `e` outside the triangle and affine doubling relation `2g_e=h+g_p+g_q` |
| `exists_six_distinct_pure_centers_of_triangle_all_zero` | reduces an all-zero exact omission triangle to three pairwise-distinct external pure centers, hence a canonical six-coordinate affine doubling configuration |
| `nonzero_three_torsion_of_two_adjacent_heavy_opposites`, `three_dvd_of_two_adjacent_heavy_opposites_zmod` | shows that two adjacent heavy opposites produce a nonzero coordinate difference killed by `3`; cyclically this forces `3 ∣ N`, so `(0,2,2)` is impossible at every modulus prime to `3` |
| `exists_double_difference_eq_target_of_triangle_zero_two_two`, `four_dvd_of_double_eq_half`, `twelve_dvd_of_triangle_zero_two_two_zmod` | strengthens the exact `(0,2,2)` profile: the pure companion on its zero edge has displacement `x` with `2x=N/2`, forcing `4 ∣ N`; together with adjacent-heavy 3-torsion this forces `12 ∣ N` |
| `witness_neg_pair_sum_at_zero_of_le_one`, `not_two_adjacent_heavy_opposites_of_involution`, `not_two_adjacent_heavy_opposites_at_half_zmod` | closes the branch completely: two adjacent pure heavy witnesses sum to `(1,-2,1)`, whose negative is the forbidden zero-witness `(-1,2,-1)`; consequently `(0,2,2)` is impossible at every even cyclic modulus, superseding its conditional torsion/descent analysis for G1 |
| `witness_two_coeff_sum_le_two_of_exact_pair`, `not_two_adjacent_opposites_of_sum_ge_three`, `triangle_other_opposites_zero_of_opposite_eq_two` | generalizes the sign-flip closure: adjacent opposite coefficients with total at least `3` are impossible, since at most one unit of their positive mass remains off the triangle; hence any opposite `2` forces both neighbors to be `0`, closing `(0,1,2)` and leaving only `(0,0,2)` among profiles containing `2` |
| `G1ThreeDescent.lean`: `pair_descent_order_three`, `exists_validTuple_quotient_of_two_adjacent_heavy_opposites` | gives a generic order-three descent: delete two coordinates differing by nonzero 3-torsion and quotient by their difference, producing a valid tuple two coordinates shorter in a group three times smaller; the adjacent-heavy specialization is retained algebraically but is no longer needed for half-target G1 |
| `quotOrderThreeEquivZMod`, `exists_validTuple_third_of_two_adjacent_heavy_opposites` | identifies a cyclic order-three quotient with `ZMod (N/3)`; this remains reusable when a genuine order-three coordinate pair arises outside the now-closed adjacent-heavy half-target profile |
| `UniqueSums.lean`: `valid_gap` | the SI set is valid at every endpoint $`2^n-2^t`$ with $`2^t\le n`$ |
| `OddOrder.lean`: `chain_order_eq`, `chain_quotient_card_bound_of_joint_dissociated` | exact SI-chain order and automatic residual separation for a chain embedded in a dissociated family |
| `codim_one_chain_odd_card_bound` | a chain missing one coordinate already forces the full odd threshold |
| `mersenne_certificate_order_eq`, `mersenne_certificate_card_bound_of_span` | chain-free Mersenne certificate: dissociation supplies the order lower bound, while coordinatewise annihilation and spanning force the exact Mersenne order |
| `RelationCertificate.lean`: `det_zsmul_eq_zero_of_matrixRelations`, `mersenne_card_bound_of_relation_matrix` | adjugate bridge from an integer relation matrix of determinant `±(2^(m+1)-1)` to the full odd threshold; includes the determinant-15 torsion certificate |
| companion `unique` census: `scripts/relation-certificate-census.py` | exact threshold validation: every SHC tuple mod 15 and 31 has a Mersenne determinant certificate; the mod-35 stress test shows the extraction statement must retain its strict-window hypothesis |
| companion `unique` census: `scripts/strict-window-witness-census.py` | all 10,496 dissociated four-coordinate tuples at odd orders 17–29 have a forbidden head-2 relation; every deletion-saturated tuple has a unit coordinate, giving the next normalization target |
| companion `unique` census: `scripts/five-window-witness-census.py` | all 1,692,224 dissociated five-coordinate tuples among 28,779,982 candidates at odd orders 33–61 have a forbidden head-2 relation; 448 saturated tuples at 45 and 55 lack a unit, so the next generator reduction must use SHC rather than saturation alone |
| `SubtupleRigidity.lean`: `shc_deleted_span_eq_top` | assuming the lower-dimensional odd cyclic SHC bound, every coordinate deletion in the next strict window spans the ambient cyclic group |
| `SHCBaseCases.lean`: `cyclicSHCOddLowerBound_three`, `shc_four_deleted_span_eq_top` | kernel-reduced exclusions at orders 9, 11, and 13 prove the three-coordinate bound 15 and make four-coordinate deletion spanning unconditional through order 29 |
| `SHC.normalize_generator`, `not_exists_shc_of_normalized` | a generator coordinate can be reindexed and identified with `1` in `ZMod (|G|)`; a normalized finite exclusion then rules out the original SHC family |
| `SHCFourBaseCases.lean`: `normalized_shc_four_excluded_of_odd_window` | kernel-reduced sorted normalized exclusions for every odd modulus 17–29; dissociation plus the head-2 shell clause already contradict each other |
| `SHCFourGenerator.lean`: `cyclicSHCOddLowerBound_four`, `odd_min_five`, `shc_five_deleted_span_eq_top` | generator-coordinate existence at every odd order 17–29 closes the normalized reduction, proving the unconditional four-coordinate bound 31, G2 for valid five-tuples, and five-coordinate deletion spanning through order 61 |
| `SHCFiveGeneratorReduction.lean`: `shc_hasGeneratorCoordinate_zmod_five_of_odd_window_ne_forty_five` | subgroup-coordinate counts derived from the 15/31 cyclic SHC bounds force a generator at every odd order 33–61 except the unique tight partition at 45 |
| `SHCFiveGenerator.lean`: `shc_hasGeneratorCoordinate_zmod_forty_five`, `shc_hasGeneratorCoordinate_zmod_five_of_odd_window` | the tight order-45 `3+2` subgroup split is impossible by a quotient-pigeonhole contradiction to dissociation, completing generator-coordinate existence throughout the full five-coordinate strict window |
| `SHCFiveCertificate.lean`, `Generated/SHCFiveN*.lean`, `SHCFiveBaseCases.lean` | complete normalized five-coordinate window (33 analytically, every odd order 35–61 by generated certificates), the unconditional cyclic SHC bound 63, `odd_min_six`, and six-coordinate deletion spanning through order 125 |
| `SHCSixGeneratorReduction.lean`: `shc_hasGeneratorCoordinate_zmod_six_of_odd_window_ne_exceptions` | lower-dimensional SHC bounds force a generator coordinate at 27 of the 31 odd orders 65–125; the subgroup-cover method isolates exactly 75, 99, 105, and 117 as its tight exceptions |
| `SHCSixGenerator.lean`: `shc_hasGeneratorCoordinate_zmod_six_of_odd_window_ne_one_hundred_five` | quotient-pigeonhole contradictions close the tight two-prime cases 75, 99, and 117, proving generator-coordinate existence at 30 of 31 window orders; only the three-prime order 105 remains |
| `SHCSixExceptionalCertificate.lean`, `Generated/SHCSixN105*.lean`, `SHCSixGeneratorComplete.lean` | the exact-three subgroup argument reduces order 105 to 3,478,761 sorted normalized nonunit tails; 1,326 generated blocks use 208,601 kernel-checked decision-tree branches to exclude them, completing generator-coordinate existence at every odd order 65–125 |
| `SHCCardinality.lean`: `shc_card_ge_cube_add_two_doubles`; `SHCSixCardinality.lean`; `SHCSixCertificate.lean`; `Generated/SHCSixNormalizedN*.lean`; `SHCSixBaseCases.lean` | a uniform cube-plus-doubles injection proves `|G| ≥ 2^m + 2m` for every SHC family with `m ≥ 3`; the isolated analytic corollary closes the six-coordinate normalized window through 75 (6 of 31 odd cases), while the generated 67/69 certificates remain independent kernel-checked cross-checks; orders 77–125 and the full six-coordinate SHC bound remain open |
| `QuadraticWedge.lean`: `shc_diff_of_valid` | every valid anchored tuple satisfies SHC |
| `bottom_wedge_of_valid`, `quadratic_wedge_of_valid` | linear and quadratic wedges stated directly for valid tuples |
| `shc_shift_target_card_gt` | a $`2h_x`$ shift cannot increase subset-sum level |
| `GlobalRoadmap.lean` | definitions of G1/G2/G3, predicate transport and endpoint existence, the G1 descent dichotomy, and the proof that G1+G2+G3 imply all stratum bounds and Conjecture 1 |

The outstanding mathematical statements are the full common-touch theorem
(G1), the complete odd-stratum lower bound (G2), and the exceptional lift
obstruction at $`2B(n-1)`$ (G3).

## Deviations from the paper proof

* **Theorem B** constructs the four witness representations directly by
  induction on bit-width with a parity split, instead of certifying them
  via `s_min`/popcount.
* **Theorem A** avoids popcount entirely and follows the paper's §5
  route directly. `gmin w M` (binary digits of `M` below bit `w`, plus the
  whole quotient on the top coin) is defined by the one-bit-peeling recursion
  `gmin (w+1) M = M % 2 + gmin w (M / 2)`, so every proof is an induction
  whose steps only use literal `/2`, `%2` — `omega` handles all arithmetic.
  `gmin_step` is the paper's Lemma 4 (subtraction encoded as
  `M' + 2^t = M + 2^{w+1}`), proved by bit-peeling with a parity split;
  `slack` iterates it over `j` from the base `gmin_ones`. No range
  restriction on `j`, no `Nat.log` case analysis, no small-`n` evaluations.
* Lemma 2 (`ones_unique`) is a descent on the bottom coin: parity forces
  `k 0 = 1 + 2t`, and `gmin_le_dsum` + `gmin_add_le` force `t = 0`.

## Formalization notes (kept for reference)

- `omega` treats `2^w` as an **opaque atom**, but *does* abstract nonlinear
  products (`j * N`) as atoms — provide bridging equations by `ring` and let
  omega finish linearly. Corners that are vacuous on paper via pow semantics
  need explicit case splits feeding omega the reduced facts.
- Mathlib v4.32 names: `Nat.lt_two_pow_self` (argument implicit),
  `Function.update_of_ne` / `Function.update_self`,
  `Nat.log_eq_of_pow_le_of_lt_pow` for concrete `Nat.log` values (does **not**
  reduce by `decide`). Note `Finset.range_subset` now means
  `range n ⊆ s ↔ ∀ x < n, x ∈ s`; the `range m ⊆ range n ↔ m ≤ n` form is
  `Finset.range_subset_range`.
- Goals of the form `val w (fun i => …) = …` are stated about a lambda;
  `rw`/`omega` need the beta-reduced shape — open such proofs with `show`,
  or reuse `shift_*` through a pointwise `Finset.sum_congr`.
