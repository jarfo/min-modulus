# Six-point obstruction to an unrestricted cubic interpolation bound

Let K have characteristic two and let w satisfy w²+w+1=0. The six points

```
(1,1,1), (1,w,1), (1,w+1,w+1),
(1,w+1,w), (1,w,w+1), (1,1,w)
```

are distinct and have no zero coordinates. For every homogeneous cubic f,

```
w * sum_i f(P_i) = coefficient of x*y*z in f.
```

The file proves this first for all ten cubic monomials, then for arbitrary
homogeneous cubics by linearity. It constructs the required w in
`GaloisField 2 2`, so the hypotheses are realized. The final theorem
`six_point_cubic_counterexample` combines the interpolation, distinctness,
nonzero coordinates and weight, and the inequality 6 < 2³−1.

This disproves the unrestricted claim that squarefree degree-n coefficient
extraction by distinct torus points with a common nonzero weight always
requires at least 2^n−1 points. The example leaves open the version restricted to the odd cyclic orbits
that arise from min-modulus characters. The example is not a
valid-tuple or odd cyclic-orbit counterexample. It does not settle G2 or
any other main research gate.

The standalone source lives at `research/CharTwoSixPointInterpolation.lean`
in the Lean repository. It is outside the default library and adds no
imports or build jobs to the main proof. From a built checkout, run:

```sh
lake env lean research/CharTwoSixPointInterpolation.lean
```

Verification on both revisions and the complete axiom/type records are
preserved in the [companion research archive](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/char-two-research).
The main conjecture and G1/G2/G3 remain open.

## Symmetric products and Frobenius

[SymmetricProductDependence.lean](SymmetricProductDependence.lean) proves
that the seven nonempty squarefree symmetric products for the valid tuple
(0,1,3,7) modulo 15 are dependent. Replacing the last product by the square
of the first gives seven independent vectors. Both revisions verify the
same twelve audited types with standard axioms. The
[companion archive](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/symmetric-product-research)
records the exact relation, the local repair, and bounded experiments on
the still-unproved Frobenius-span approach to G2. No default imports or
main research gates change.

## Anchored-cube intersection bounds

The [anchored-cube intersection certificate](AnchoredIntersectionCounterexample.lean)
refutes uniform pairwise-quarter and triple-eighth bounds for valid tuples
at odd modulus. For (0,11,8,6) modulo 15, the selected intersections have
five and three elements, exceeding four and two. The anchored union still
fills all fifteen residues. Both Lean revisions verify identical types
and standard axioms. Exhaustive tests cover dimensions 2–6 and odd moduli
through 63; some pair satisfies the quarter bound in every tested set,
but that weaker existence statement remains unproved.

## The surviving anchored-pair route

[AnchoredPairLowerBound.lean](AnchoredPairLowerBound.lean) proves that one
intersection of size at most `2^(n-2)` forces `N >= 3*2^(n-2)` for a valid
length-n tuple, n>=2. The small-pair inequality is an explicit hypothesis;
its existence at odd moduli remains unproved. Both Lean revisions pass,
with four literal type and standard-axiom comparisons. This standalone
file adds no default-library jobs.

Additional seeded tests sample 100,000 sets in each of dimensions seven
and eight, finding 426 and six valid sets respectively. Every valid sample
has some quarter-sized pair intersection. An independent Python checker
confirms all validity and intersection results. These samples are not
exhaustive; the small-pair existence claim remains open.
[Reproduction data](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-intersections-research/higher-dimensional-sampling).

## Adaptive anchored-union increments

[AnchoredIncrementObstruction.lean](AnchoredIncrementObstruction.lean) proves
that no anchor order for the canonical valid seven-tuple modulo 127 can
add at least 64,32,16,... new points successively. A qualifying pair covers
100 points, while every triple covers at most 115. The full union nevertheless
fills 127 residues, and the natural order meets the weaker cumulative targets.
Both Lean revisions pass all fifteen literal type and standard-axiom checks.
This eliminates the separate-increment strategy; the cumulative strategy
and the full G2 bound remain open. No default build jobs are added.
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-increment-research).

## Anchored-overlap multiplier relations

[AnchoredOverlapMultipliers.lean](AnchoredOverlapMultipliers.lean) proves that
nonzero overlap forces a ternary relation with anchor multiplier 2 through n.
It also proves that multiplier one is impossible, and that one relation-free
pair implies N >= 2^n - 1. Existence of that pair is an explicit hypothesis;
the general G2 theorem remains open. Both Lean revisions pass 18 literal
type and standard-axiom checks. The corrected parallel runs reproduce 605
relation-free ordered-pair occurrences, not the 632 claimed in their summary;
all intersections are {0}. The converse is false because the search omits
subset-cardinality constraints. No default build jobs are added.
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-multipliers-research).

## Cardinality-compatible anchored relations

[AnchoredCompatibleRelation.lean](AnchoredCompatibleRelation.lean) proves an
exact criterion for nonzero cube overlap: disjoint off-anchor signed supports
P,Q must admit a relation with 2 <= M, |Q| <= M and M+|P| <= n. Both directions
are proved by extracting subset supports and reconstructing subsets of the
required size. Absence of a compatible relation is equivalent to intersection
{0} and gives N >= 2^n-1. Existence of such a pair remains an explicit input.
Both Lean revisions pass ten literal type and standard-axiom checks. A related
binomial counting formula passes all 6,668 previously sampled ordered pairs;
the general formula is now proved in [AnchoredIntersectionCount.lean](AnchoredIntersectionCount.lean).
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-compatible-research).

## Exact anchored-intersection counts

[AnchoredIntersectionCount.lean](AnchoredIntersectionCount.lean) proves the
exact binomial-weight formula for every valid tuple. Normalized subset pairs
are in bijection with disjoint signed supports P,Q and a shared selector U;
for fixed |U|=r, the weight is binomial(n-|P|-|Q|,r), and the multiplier is
|Q|+r. The proof establishes both inverse maps and counts each fibre, so no
common point is counted twice. Identical source passes both Lean revisions
with all 28 literal type and standard-axiom audits. Bounding this sum for
suitable anchor pairs remains open; the identity alone does not prove G2.
[Evidence](https://github.com/jarfo/unique/tree/main/papers/min-modulus/prove2me/anchored-intersection-count-research).
