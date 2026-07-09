# min-modulus — Lean proof for the minimum-modulus paper

This repository is the Lean 4 formalization accompanying the paper

> José A. R. Fonollosa, *Minimum modulus for the unique multiset-sum problem,
> with an application to computing the permanent*, arXiv:XXXX.XXXXX, 2026.

The main theorem of the paper is kernel-checked end-to-end: `nmin_eq` builds
with **0 errors, 0 sorries** and uses only the standard axioms
(`propext`, `Classical.choice`, `Quot.sound`, checked with `#print axioms nmin_eq`).

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
CP-certified for $`n \le 7`$) and is not formalized.

## Build

| | |
|---|---|
| File | `lean/MinModulus/Basic.lean` (~940 lines, single file) |
| Toolchain | Lean 4 `v4.15.0`, Mathlib pinned `v4.15.0` (prebuilt cache) |
| Build | `cd lean && lake build` — green (0 errors, 0 sorries) |
| Axioms | `propext`, `Classical.choice`, `Quot.sound` only |

```sh
export PATH=$HOME/.elan/bin:$PATH
cd lean && lake build   # ~seconds warm; Mathlib comes from the cache in lean/.lake
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
- Mathlib v4.15 names: `Nat.lt_two_pow_self` (argument implicit),
  `Function.update_of_ne` / `Function.update_self`,
  `Nat.log_eq_of_pow_le_of_lt_pow` for concrete `Nat.log` values (does **not**
  reduce by `decide`).
- Goals of the form `val w (fun i => …) = …` are stated about a lambda;
  `rw`/`omega` need the beta-reduced shape — open such proofs with `show`,
  or reuse `shift_*` through a pointwise `Finset.sum_congr`.
