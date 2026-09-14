# Exact arbitrary-degree translation counts from disjoint cores

A degree-k translation match is a pair (S,T) of k-element subsets of A
with sum(S)+t=sum(T). Its core is (U,V)=(S\T,T\S), and its common
support is H=S intersect T. Then U and V are disjoint, |U|=|V|<=k,
sum(U)+t=sum(V), and H is a (k-|U|)-subset of A\(U union V).
Conversely the core and H uniquely reconstruct S=U union H and
T=V union H.

The new definition squarefreeTranslationCores records exactly these
possible cores. Four original proofs establish its membership criterion,
extract the core data from a match, prove the exact counting identity,
and apply nonuniform weighted packing:

    |squarefreeTranslationMatches(g,A,k,t)|
      = sum_(U,V) in cores choose(|A|-2*|U|, k-|U|).

The definition, core extraction and exact count need no tuple validity
or injectivity assumption. Validity makes this count equal to the
translated squarefree value intersection through the existing theorem.

For a valid tuple, any M that bounds

    choose(|A|-2*j, k-j) * choose(2*j, j)

for every core size j present also bounds the number of translation
matches. This is the precise numerical premise still to be controlled;
it is not asserted uniformly sharp enough for the central-degree target.
The separate fixed-union cap may improve estimates rank by rank.

All four original proofs, nine exact declaration types and three
definition values pass both installed Lean/Mathlib revisions with only
standard axioms. The two existing definitions are ValidTuple and
squarefreeTranslationMatches; squarefreeTranslationCores is new.

No finite enumeration campaign is used. The central-degree numerical
inequalities and unrestricted G1/G2/G3 remain open.
Split Prove2Me export and private publication remain.
