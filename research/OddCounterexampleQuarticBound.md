# Quartic growth inside a hypothetical large odd counterexample

Let g be a valid tuple of dimension n>=144 at odd modulus N, and suppose
N<2^n-1. Write E for disjointDoubledDifferencePairs(g), the unordered anchor
pairs whose doubled difference has a coordinate representation outside
the anchor pair.

The complement D of E in the two-element coordinate subsets covers
every unrepresented doubled difference. The proved dense-case obstruction
gives 3*choose(n,2)<=(n-9)*|D|. Since |D|+|E|=choose(n,2), this implies

    (n-9)*|E| <= (n-12)*choose(n,2).

This is exactly the sparsity hypothesis of the earlier quadratic-count
quartic theorem. Therefore the hypothetical counterexample satisfies

    |repeatedCoinCover(g,4)| >= choose(n+1,2)+choose(n,3).

The result links the dense affine-domain proof chain to repeated-sum
growth. The small-modulus counterexample premise remains explicit, and
the quartic consequence does not prove the central-degree inequalities
required for generic G2. Existing small-dimension results are unchanged.

Three original proofs, eight exact declaration types and three existing
definition values pass both installed Lean/Mathlib revisions with standard
axioms only. No new definition or finite enumeration is introduced.
Generic G1/G2/G3 remain open. Split Prove2Me export and publication remain.
