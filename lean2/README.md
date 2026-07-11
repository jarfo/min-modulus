# Lean2

This is a Lean project to formalize the proof of Proposition 2
(optimality among elementary abelian $2$-groups) in the paper

> José A. R. Fonollosa, *Minimum modulus for the unique multiset-sum problem*,
> [arXiv:2607.08366](https://arxiv.org/abs/2607.08366), 2026.

The Lean proof follows the pencil-and-paper proof sketch in the paper.

Target statement:

If $g_0, \dots, g_{n-1} \in (\mathbb{Z}_2)^k$ have unique multiset sums, then
$k \ge n - 1$. Equivalently, the least elementary abelian $2$-group admitting
such a family has order $2^{n-1}$.

## Build

```sh
export PATH=$HOME/.elan/bin:$PATH
cd lean2
lake exe cache get   # fetch the prebuilt Mathlib cache
lake build
```

## Verification status

Checked on 2026-07-11 (Lean 4.31.0, Mathlib pinned in `lake-manifest.json`):

- `lake build` compiles cleanly; no `sorry` or custom axioms. `#print axioms`
  reports only `propext`, `Classical.choice`, `Quot.sound`.
- The theorem `Lean2.elementaryAbelianTwoGroups_optimal` in `Lean2/Basic.lean`
  matches Proposition 2 of the paper: `UniqueMultisetSums` quantifies over
  multiplicity vectors $m : \mathrm{Fin}\ n \to \mathbb{N}$ with
  $\sum_i m_i = n$, and casting $m_i$ into $\mathbb{Z}_2$ before scaling gives
  the correct multiset sum in $(\mathbb{Z}_2)^k$. The conclusion `n - 1 ≤ k`
  (truncated subtraction) is equivalent to $k \ge n - 1$.
- The proof follows the paper's argument: the map
  $\Lambda(x) = \sum_i x_i g_i$ and the coordinate-sum functional are built as
  linear maps; a nonzero $u \in \ker \Lambda \cap \ker(\mathrm{sum})$ has even
  positive support $S$, and doubling half of $S$ while dropping the other half
  yields a size-$n$ multiset with the same group sum but a multiplicity
  $\ne 1$, contradicting uniqueness; rank–nullity then gives
  $n = \operatorname{rank} \Lambda + \dim \ker \Lambda \le k + 1$.
- The hypothesis is non-vacuous: $n = 2$, $k = 1$, $g = (0, 1)$ satisfies it
  and meets the bound with equality.
