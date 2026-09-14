# Verified all-anchor CR1 equivalence

The central repeated-cover target has an exact all-anchor outside-cube
formulation. For any valid g and anchor q, put h_i=g_i-g_q and let B
be the entire subset-sum cube avoiding q. In every degree k>=0,

    |D_k(g)|+1 >= sum_(j<k) choose(n,j)
        iff
    |C_k(h) outside B|+1 >= sum_(j<k) choose(n-1,j).

Four new original proofs retain Pascal boundary terms, prove the zero-anchor
equivalence, establish repeated-cover translation invariance and obtain
the all-anchor equivalence. A fifth exported theorem is the exact existing
squarefree/repeated count |C_k|=choose(n,k)+|D_k|, previously used inline.
Neither inequality is asserted to hold. The central outside count and
G1/G2/G3/CR1 remain open. No new counting hypothesis is assumed.
The new proofs are in OutsideCubeRepeatedBounds.lean; the existing count
is in RepeatedCoinGrowth.lean.

Both revisions verify five target types and dependency sets, three
external theorem interface types, four existing definition values and
five exact original inline helper types, including the subset-sum
helper definition value. No new definition bundle is introduced. Exact
parser spans retain every original proof body. Metadata and live preflight
pass; private publication is pending. One supporting root retains the
all-anchor equivalence and its exact counting chain.
