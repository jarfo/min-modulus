import MinModulus.G2OddSmallDimensions

/-!
# The anchored subset-sum union: a conjectural route to G2

For a tuple `g : Fin n → ZMod N` and an anchor `k`, the anchored cube
`C_k = { ∑_{j ∈ S} (g j - g k) : S ⊆ Fin n }` is the set of subset sums of the
translate `g - g k`; it has `2^(n-1)` elements when `g` is valid.  The
**anchored union** is `U = ⋃_k C_k`.

Conjecture (odd anchored union).  If `N` is odd and `g` is valid, then
`2^n - 1 ≤ |U|`.  Since `U ⊆ ZMod N`, this implies G2 directly
(`oddStratumLowerBound_of_anchoredUnion` below).

Evidence (2026-09-11, `explore/union_conj.py`, `explore/union_strata.py`):
random valid sets for `n = 4, 5, 6` and odd `N` up to `99` all satisfy the
bound, with equality `|U| = N = 2^n - 1` exactly on the super-increasing sets
`(0, 1, 3, …, 2^(n-1) - 1)`, which also need all `n` anchors.  For the
super-increasing set the residue with binary digits `b` is hit by exactly
`n - popcount(b)` anchor/subset pairs.

Two natural strengthenings are false: the even analogue `stratumBound n s ≤ |U|`
fails at `(n, N) = (5, 30)` (a valid set with `|U| = 29`), and the
system-of-distinct-representatives form (an injective choice of anchor
`k(S) ∉ S` for the `2^n - 1` proper subsets) fails for composite odd `N`
such as `15, 21, 27, 35, 45, 49`.  Canonical anchor rules (`min`/`max` of the
complement, by index or by value) never work.

No fixed family of coefficient vectors can replace this: the largest family
whose pairwise differences are excluded for every valid odd-modulus tuple
has size exactly `2^m + 2m` for `m = n - 1 ≤ 4` (exhaustive clique search over
entries in `[-2, 3]`, `explore/family_clique.py`), the bound already proved by
`card_ge_of_odd`.  A generic proof of G2 must therefore use tuple-dependent
structure, as the anchored union does.

This file records the conjecture and its checked connection to G2.  It is
a *stronger* open input than G2 and is deliberately not uploaded as a
platform node.
-/

namespace MinModulus
open Finset

variable {n N : ℕ}

/-- The subset sums of the translate `g - g k`. -/
def anchoredCube [NeZero N] (g : Fin n → ZMod N) (k : Fin n) : Finset (ZMod N) :=
  (Finset.univ : Finset (Finset (Fin n))).image (fun S ↦ ∑ j ∈ S, (g j - g k))

/-- The union of the anchored cubes over all anchors. -/
def anchoredUnion [NeZero N] (g : Fin n → ZMod N) : Finset (ZMod N) :=
  Finset.univ.biUnion (anchoredCube g)

/-- **Odd anchored-union conjecture.** A valid tuple modulo an odd number has at
least `2^n - 1` anchored subset sums. -/
def AnchoredUnionLowerBound : Prop :=
  ∀ {n N : ℕ} [NeZero N], Odd N → ∀ g : Fin n → ZMod N, ValidTuple g →
    2 ^ n - 1 ≤ (anchoredUnion g).card

/-- The anchored-union conjecture implies G2: the union lives inside `ZMod N`. -/
theorem oddStratumLowerBound_of_anchoredUnion (h : AnchoredUnionLowerBound) :
    OddStratumLowerBound := by
  intro n N hN hv
  obtain ⟨g, hg⟩ := hv
  haveI : NeZero N := ⟨hN.pos.ne'⟩
  have hcard := h hN g hg
  have hle : (anchoredUnion g).card ≤ N := by
    simpa only [ZMod.card] using Finset.card_le_univ (anchoredUnion g)
  omega

end MinModulus
