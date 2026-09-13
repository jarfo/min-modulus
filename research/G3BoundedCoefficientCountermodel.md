# Bounded coefficient tests cannot close generic G3

`G3BoundedCoefficientCountermodel.lean` strengthens the preceding balanced
countermodel. For every fixed natural number C, and every non-power-of-two
n with n >= 2^(C+4), the actual G3 exceptional modulus admits an **invalid**
tuple g with the following isolation property:

```
sum c_i = 0,   sum c_i g_i = 0,   -1 <= c_i < C for every i
    imply c = 0.
```

The tuple is g_i = 2^i. Its invalidity is already proved in
`G3BalancedCountermodel.lean`. This is not a counterexample to the
min-modulus conjecture. It shows that no fixed coefficient cutoff captures
the full validity assumption needed by this proposed G3 route.

## Exact classification behind the result

For any s < n, put N = 2^n - 2^s and consider a natural multiset k of exactly
n binary coins, congruent to the all-ones target 2^n - 1 modulo N.
The new classification proves that either k is all ones, or its ordinary
integer value is exactly 2^s - 1.

There is only one possible downward wrap, since 2N > 2^n - 1. An upward
wrap by jN requires at least n+j coins, by the existing generic `slack`
and `gmin_le_dsum` lemmas. No enumeration or finite tuple search is used.

A rival therefore uses only the s positions below the removed power.
If every multiplicity k_i is at most C, it has at most C*s coins. Thus
n > C*s excludes every such rival. In signed coordinates c_i = k_i - 1,
this is precisely the isolation property for -1 <= c_i < C.

At the G3 modulus, s = floor(log2 n)+1. The proof supplies the explicit
sufficient threshold n >= 2^(C+4) for C*s < n. This threshold is convenient,
not claimed optimal. The countermodel still has an admissible nonzero
zero relation; some positive coefficient must escape the chosen cutoff.

## Antichain restriction also survives

The existing negative-support antichain proof compares two unit witnesses
c and d at a common target. Under nested negative supports, c-d has all
coefficients in [-1,2]. The new proof records that bounded isolation with
C=3 suffices for that comparison; it does not need full validity.

For every n >= 16, 3*(floor(log2 n)+1) < n. Consequently, at every G3
dimension in this range, the invalid binary tuple satisfies, for every
target h and every finite family of unit witnesses at h:

* the negative-support map is injective;
* its image is an antichain;
* the family has size at most choose(n,floor(n/2)).

The theorem `exceptional_antichain_countermodel` proves these assertions
together with invalidity. This strengthens the earlier note, which
correctly left the antichain question unresolved. It does not assert the
same result below dimension sixteen.

## Consequence for the next proof

Balanced quotient collisions, compatible unit families, and these
same-target antichain bounds cannot by themselves yield the generic G3
contradiction. Increasing a constant coefficient cutoff cannot repair
that inference: the explicit family eventually passes every fixed cutoff.
An argument through admissible relations must use constraints whose
coefficient range grows with n, or introduce additional structure that
does not follow from bounded isolation. This is a limitation of the
listed necessary conditions, not an impossibility claim about all G3
proof methods.

G1, G2, G3 and the arbitrary-n conjecture remain open.

## Verification

Ten new theorems are checked on both the repository and supported
Prove2Me Mathlib revisions. Sixteen literal declaration types and the
values of six shared definitions match between revisions. The axiom
audit permits only `propext`, `Classical.choice`, and `Quot.sound`.

* Repository: Lean 4.32.0, Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997`.
* Supported: Lean 4.33.1, Mathlib
  `0df444a360eaa60ab8c11dca51a86af692955474`.

The checker reuses the exact previously compiled full `UniqueSums`
dependency and the preceding balanced-countermodel proof. It runs at
most two Lean jobs with two compiler threads each. No platform theorem
nodes are uploaded for this local research file.
