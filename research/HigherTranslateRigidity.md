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
