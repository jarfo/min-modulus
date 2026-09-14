# Exact repeated representations inside an anchored cube

The generic-n conjecture and G1/G2/G3/CR1 remain open. This module proves
three structural facts about the cube portion of the coin cover. It does
not supply the missing outside-cube lower bound.

Let g be a valid tuple, choose a zero anchor q with g(q)=0, and let B be
all subset sums avoiding q. Write C_k for all values of multisets of k
coordinates and D_k for values admitting a repeated coordinate. No
oddness assumption is needed.

For any subset S avoiding q, its sum belongs to D_k exactly when
|S|+2 <= k. At degrees at most |S|, the shortest-representation rigidity
forces the multiset to be S. At degree |S|+1, validity forces it to be
the squarefree set S union {q}. From degree |S|+2 onward, adding at least
two zero-anchor coins gives a repeated representation.

Consequently, for every k >= 0,

    |B intersection D_(k+2)| = sum_(j=0)^k choose(n-1,j).

The proof identifies this intersection with B intersection C_k before
applying the existing exact cube filtration count.

Finally, suppose i belongs to S and sum(S)+g(i)=sum(T), where T avoids q.
Then |T| < |S|. Duplicating a member of S therefore either leaves the
anchored cube or lands in a strictly smaller subset layer. The theorem
does not require S itself to avoid q.

This strict decrease is relevant to a possible counting argument using
all duplicated subset sums. It does not prove that their contributions
outside B are independent, nor that different subsets give different
outside values. Those are unresolved mathematical questions.

Both Lean/Mathlib revisions pass: three proofs, eleven exact declaration
types, four definition values and only standard axioms.
All three exported theorem nodes are private and Proved on Prove2Me. The split export,
exact proof-source readbacks and consolidated dependency audit pass. See
[the verified chain](RepeatedAnchoredCubeFiltrationResearch.md).
