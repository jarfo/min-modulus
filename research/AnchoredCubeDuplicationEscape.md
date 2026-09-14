# Every anchored subset has an escaping duplication

For every valid tuple at odd cyclic modulus, every zero anchor q and
every nonempty subset S avoiding q, some member i of S satisfies

    sum(S) + g(i) is outside the entire anchored subset-sum cube.

The theorem holds in arbitrary dimension and at every subset size. The
first version assumes injective doubling explicitly; the odd-modulus
corollary supplies it. Neither a closure hypothesis nor a bound on cube
intersections is assumed.

Suppose instead that every duplication returns to the cube, with target
subset T_i. The repeated filtration theorem gives |T_i|<|S|. The target
T_i cannot contain i: removing i would represent sum(S) by fewer coins.
Choose a target T_i of maximum size. If another j in S is absent from
T_i, compare the squarefree set T_i union {j} with the multiset obtained
by adding i to T_j. Their sums agree and the latter has no more coins.
Shortest-representation rigidity makes the multisets equal, incorrectly
putting i into T_i union {j}. Thus T_i contains S without i. The strict
size bound forces equality, which makes 2*g(i)=0. Injective doubling
then gives g(i)=0, contrary to validity and i differing from the anchor.

This proves that no nonempty subset has an empty set of outside
duplication values. It does not show that different subsets have distinct
escapes, or that the proposed matrix columns are linearly independent.
The aggregate central outside-cube count and G1/G2/G3/CR1 remain open.

Both Lean/Mathlib revisions pass: two proofs, seven exact declaration
types, two definition values and only standard axioms.
Both exported theorem nodes are private and Proved on Prove2Me. The split export,
exact proof-source readbacks and consolidated dependency audit pass. See
[the verified chain](AnchoredCubeDuplicationEscapeResearch.md).
