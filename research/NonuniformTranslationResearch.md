# Nonuniform translation packing and exact core counts

Eight generic lemmas combine nonuniform translated-support packing with
an exact arbitrary-degree count of squarefree translation matches.

For disjoint equal-evaluation pairs with fixed cardinality gap, separating
permutation events are disjoint even when support sizes vary. Natural
weights w satisfying w*choose(|U|+|V|,|U|)<=M therefore have sum at most M.
With injective doubling, a fixed union determines a pair of prescribed
first-side size and signed value; a balanced size-j family supported in A
has at most choose(|A|,2*j) members.

Every degree-k translation match decomposes uniquely into disjoint
differences U,V and a common support H outside their union. Thus

    |matches| = sum_(U,V) in cores choose(|A|-2*|U|,k-|U|).

This identity needs no validity assumption. For valid tuples, any M
bounding choose(|A|-2*j,k-j)*choose(2*j,j) at every core size present
bounds the match count. This numerical premise is explicit; sufficient
central-degree estimates and unrestricted G1/G2/G3 remain open.

The original proofs are in NonuniformTranslatedPacking.lean and
SquarefreeTranslationCoreCount.lean. The new definition bundle contains
the original separating-permutation event definition (previously inline)
and the new squarefreeTranslationCores definition.

The split export passes both revisions: eight exact original target
types and dependency sets, three external interface types, eight original
inline helper types and four definition values match. Exact parser spans
retain all original proof bodies. Metadata and live preflight pass.
Private proof publication is pending. Two supporting roots will retain
the support-union cap and the final weighted match bound.
