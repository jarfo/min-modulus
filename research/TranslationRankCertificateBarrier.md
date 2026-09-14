# A uniform limitation of the core-rank certificate

The current fractional certificate combines a shared budget with rank
caps. If one rank r has capacity C_r at least its packing denominator
B_r, its certificate inequality already forces the total objective to
be at least B_r*w_r. This statement requires nonnegative residual terms
beta_j but does not require alpha to be nonnegative.

At support size2*k with k>=3, rank two has B_2=C_2=6. If it is included
in the allowed ranks, every such certificate therefore has objective

    M >= 6*choose(2*k-4,k-2).

Two central-binomial steps grow by at most a factor16. Consequently

    8*M >= 3*choose(2*k,k).

This is a symbolic limitation valid for every k>=3. It concerns the
numerical relaxation, and is not a construction of a valid tuple or a
counterexample to min-modulus. In particular, removing ranks zero and
one alone does not remove this rank-two floor. A stronger argument needs
additional compatibility of small cores or their aggregate occurrence
across anchor pairs; choosing different numerical certificate weights
cannot by itself improve past this floor when rank two remains allowed.

Four original proofs and four exact declaration types pass both installed
Lean/Mathlib revisions with standard axioms only. No new definition and
no finite enumeration or exclusion campaign is introduced. Generic
G1/G2/G3 remain open. The split export and private publication are verified below.

## Verified Prove2Me growth constraints and certificate limits

These results are included in the seven-theorem growth-constraint and certificate-limit
chain, now private and Proved. See [the consolidated chain](CounterexampleGrowthConstraints.md).
The numerical certificate premises remain explicit, and unrestricted G1/G2/G3 remain open.
