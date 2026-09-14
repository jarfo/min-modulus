# Core-rank bounds and fractional certificates

Ten generic lemmas group translation cores by size and combine two
independent cardinality caps with one shared fractional packing bound.
If c_j is the number of size-j cores supported in A, validity gives
c_j<=choose(2*j,j), while injective doubling gives c_j<=choose(|A|,2*j).
The exact match count is sum_j c_j*choose(|A|-2*j,k-j). Nonzero
translations have no empty core, so their ranks begin at one.

The shared rational inequality is sum_j c_j/choose(2*j,j)<=1. Thus
any alpha>=0 and beta_j>=0 with

    choose(|A|-2*j,k-j) <= alpha/choose(2*j,j)+beta_j

give the match-count bound

    |matches| <= alpha + sum_j min(choose(2*j,j),choose(|A|,2*j))*beta_j.

Every sum is over an explicit finite cover of the core ranks. The
certificate hypotheses are explicit; no certificate sufficient for the
central-degree goal is supplied. Unrestricted G1/G2/G3 remain open.
The original proofs are in SquarefreeTranslationCoreRanks.lean and
NonuniformTranslationFractional.lean.

The split export passes both revisions: ten exact original target
types and dependency sets, five external interface types, seven original
inline helper types and four existing definition values match. Exact
parser spans retain all original proof bodies. No new definition bundle
is needed. Metadata and live preflight pass. Private publication is
pending. Two roots retain the positive-rank estimate and the combined
fractional certificate.
