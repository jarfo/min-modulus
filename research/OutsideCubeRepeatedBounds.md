# CR1 as an exact outside-cube target

For every valid tuple g, every anchor q and every degree k, put h_i=g_i-g_q.
Let B be the entire subset-sum cube formed from h_i with i different from q.
The repeated-cover inequality for the original tuple is equivalent to

    |C_k(h) outside B| + 1 >= sum_(j=0,...,k-1) choose(n-1,j).

The original inequality is

    |D_k(g)| + 1 >= sum_(j=0,...,k-1) choose(n,j).

Neither inequality is proved here. The equivalence includes all boundary
terms, every multiplicity pattern and every anchor. No oddness, closure or
additional counting hypothesis is needed for the equivalence itself.
At the two central degrees of CR1, the outside-cube lower bound is exactly
the missing task. This does not replace it with a proved estimate.

The proof combines three exact identities: the squarefree/repeated
partition |C_k|=choose(n,k)+|D_k|; the new disjoint cube/outside count;
and Pascal's partial-row identity. Translating g by -g_q translates every
repeated degree-k value by -k*g_q, so its cardinality stays unchanged.
Validity is also preserved under translation.

Four original proofs provide the partial-row identity, the zero-anchor
equivalence, repeated-cover translation invariance and the all-anchor
equivalence. Both Lean/Mathlib revisions pass: four proofs, eleven exact declaration
types, four definition values and only standard axioms. The central
inequality and G1/G2/G3/CR1 remain open. All five exported theorem nodes are private and Proved on Prove2Me. The split export,
exact proof-source readbacks and consolidated dependency audit pass. See
[the verified chain](OutsideCubeRepeatedBoundsResearch.md).
