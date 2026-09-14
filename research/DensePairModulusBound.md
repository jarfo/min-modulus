# Sharp odd modulus bound in the dense represented-pair regime

For a valid tuple g of length n>=144 at odd modulus N, let D be a family
of two-coordinate subsets covering every unrepresented doubled
coordinate difference. If

    (n-9)*|D| < 3*choose(n,2),

then the sharp odd threshold holds:

    2^n-1 <= N.

The proof extracts the verified one-escape affine doubling structure
and applies the existing AlmostDoubling theorem. Oddness supplies
injectivity of doubling. No cycle decomposition or finite enumeration
is needed in this final application.

The second theorem states the precise remaining alternative: if a valid
odd tuple at n>=144 has N<2^n-1, every such pair cover D satisfies

    3*choose(n,2) <= (n-9)*|D|.

Both original proofs, six exact declaration types and the ValidTuple
definition value pass the original and supported Lean/Mathlib revisions
with only standard axioms. No new definition is introduced.

This proves the sharp odd bound under an explicit missing-pair density
premise. This argument does not cover dimensions below 144; existing small-dimension
results remain valid. The sparse represented-pair regime, absolute central
inequalities and unrestricted G1/G2/G3 remain open.
Split Prove2Me export and private publication remain.
