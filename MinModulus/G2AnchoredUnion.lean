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

Exploratory computations reported by the parallel agent suggest this bound
for sampled valid tuples with `n = 4, 5, 6` and odd `N ≤ 99`. The referenced
`explore/union_conj.py`, `explore/union_strata.py`, and
`explore/family_clique.py` scripts are not tracked in that branch, so these
reports are not independently reproduced here and are not formal results.

The agent also reports counterexamples to an even-modulus analogue and to
some systems of distinct representatives. These reports motivate searching
for tuple-dependent structure; they do not prove that every fixed family
of coefficient vectors must fail. In particular, a clique search restricted
to `m ≤ 4` and entries in `[-2, 3]` cannot establish such an unrestricted
impossibility claim.

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
