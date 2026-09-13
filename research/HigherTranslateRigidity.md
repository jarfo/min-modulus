# Translate rigidity in every coin degree

The generic G2 target remains the one-step inequality

```
|C_(r+1)| <= |D_(r+2)|,
```

in the required half-degree range. Here C_d is the set of all d-coin sums
and D_d consists of those admitting a repeated coordinate. The new file
`HigherTranslateRigidity.lean` extends the existing quadratic translate
argument to every degree, using the full `ValidTuple` predicate.

For a shift t outside C_(d-1), suppose g_j+t has a squarefree degree-d
representation on a set S. Then j is not in S. Every translated coordinate
g_a+t that lies in C_d has a in S union {j}. Therefore at most d+1
coordinates can hit C_d. If there are at least d+2 hits, every hit belongs
to D_d.

The key comparison is an equality between the squarefree sum on S union
{a} and the multiset formed by adjoining j to a representation of g_a+t.
Validity identifies these multisets, contradicting j outside S union {a}.
This works in arbitrary degree and does not require an odd modulus.

A complete outside translate A+t contained in C_d, with n>=d+2, is thus
contained in D_d. Replacing one coin by its translated repeated
representation proves, for every r>=0,

```
|C_(r+1)| <= |D_(r+d)|.
```

Translation by t supplies the injection. For d=2 this recovers the
one-step repeated growth mechanism. For d>2 it is a larger degree jump,
and must not be reported as the missing one-step inequality.

The five new theorems are uniform in n and all coin degrees. Both Lean
revisions pass nine literal type comparisons, four definition-value
comparisons, and a standard-axiom audit. No finite tuple search is used.
The existence of a useful complete outside translate is not proved.
G1, G2, G3 and the arbitrary-n conjecture remain open.

Repository Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997`.
Supported Mathlib: `0df444a360eaa60ab8c11dca51a86af692955474`.

## Accepted Prove2Me statements

All five statements are private and Proved, with ACCEPTED submissions.
The exact server proof files match the locally checked split sources.
One terminal supporting root connects the whole chain to the consolidated
DAG, using the existing multiset uniqueness interface. The shared new
definition file contains only the repeated cover and translate-hit set.

* coin_translate_hit_mem_insert_of_squarefree_hit: f5022c9a-de14-471c-ad82-21203903f540
* outside_coin_translate_anchor_not_mem: 5e883d7c-c266-448b-9684-a580b795d176
* outside_coin_translate_hits_le_of_squarefree_hit: 57e46439-4a4f-4576-8d8a-bac1d5955fe4
* outside_coin_translate_hit_repeated_of_many_hits: fa8209ca-690a-43da-a04b-8df516b85c57
* repeated_coin_growth_of_full_higher_translate: e170c98c-649f-47e6-b060-c3f65787f34f

The consolidated DAG is acyclic with 876 nodes and 1982 edges. All 621
recorded proof dependency sets across 17 bundles match. G1/P6, G2/From7
and G3/From7 remain the three open leaves. Complete outside-translate
existence and generic one-step growth remain unproved.
