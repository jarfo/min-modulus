# Residual trades inside a repeated-sum fibre

Fix a valid n-tuple g in an abelian group with injective doubling. This
includes every odd cyclic group. Suppose an anchor family R has residual
supports B_a of one fixed positive size k, with

    2g_a + sum_{i in B_a} g_i = x   for every a in R.

[ResidualTradeRigidity.lean](ResidualTradeRigidity.lean) proves two
constraints on this family. Both statements are uniform in n and do not
assume a small modulus or enumerate tuples.

The first statement applies in every positive residual degree. If two
anchor subsets I,J have equal aggregate residual multisets,

    sum_{a in I} B_a = sum_{a in J} B_a,

then I=J. The sums here preserve multiplicities of coordinate indices.
Counting those multiplicities first gives |I|=|J|. Summing the fibre
equations then gives equal doubled anchor sums. Injective doubling and
validity identify the anchor subsets. Thus distinct subsets cannot form
a balanced residual trade, strengthening the earlier pairwise assertion
that individual residual supports are distinct.

The second statement concerns k=2, so the residual supports are edges
and the represented sums have degree four. A rooted residual balance is

    sum_{a in P} B_a = sum_{a in Q} B_a + [p,p],

where p lies outside R and [p,p] is a multiset containing two copies of
p. Two such balances, rooted at p and q, cannot have disjoint anchor
supports P union Q and U union V. The roots may coincide, and no
disjointness between P and Q or between U and V is assumed.

Indeed |P|=|Q|+1, and the fibre equations give

    2(sum_P g + g_p) = x + 2 sum_Q g.

Combining two balances and cancelling doubling equates the squarefree
sums on (P union V) plus p and (Q union U) plus q. If the anchor supports
were disjoint, validity would identify these coordinate sets and force
P to be contained in Q, contradicting their cardinalities.

Both proofs pass the original and supported Mathlib revisions. The two
theorem types and ValidTuple's type and definition value match exactly;
all proof axioms are standard. The source bodies are identical across
revisions. The proofs have not yet been exported or uploaded to Prove2Me.

## Proposed graph consequence, not yet formalized

In an actual single-repeat quartic fibre, the existing support-avoidance
lemma puts all residual edges outside the anchor set. Residual edges are
distinct. The first theorem excludes an even residual cycle: alternating
edges would give a nontrivial balanced residual trade. Alternating edges
of an odd cycle give the rooted balance in the second theorem, which
excludes two odd cycles with disjoint edge sets.

The intended graph argument is that a graph with no even cycle has
edge-disjoint odd cycles, so there is at most one cycle in the entire
residual graph. Its number of edges is then at most its number of
vertices, suggesting 2|R|<=n. The cycle translations, graph decomposition
and resulting fibre bound are not formal Lean results in this file.
They are the next steps to check. No new numerical fibre cap is claimed.

Even that dimension-dependent cap would leave the global repeated-sum
growth problem open. The full-rank combination of coefficient probes,
generic G2, G1 and G3 remain unresolved.

## Verified statement/proof export

Both residual-trade statements pass both revisions as separate statement
and proof files. Their two original types and two exact theorem
dependency sets match, as does ValidTuple in type and definition value.
There are no proof holes outside declared interfaces. The export
reuses one Proved theorem interface and existing definitions; it adds
no definitions or inline helpers. Both split proof bodies match the
checked source file. Metadata, exact live readbacks and unused names
pass. The two theorem nodes have not yet been uploaded. The graph
consequence and generic G1/G2/G3 gates remain open.
