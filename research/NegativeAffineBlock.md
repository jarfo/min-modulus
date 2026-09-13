# Negative affine doubling domains

These three results constrain a possible structural case in the dense
represented-difference problem. They do not claim that a dense graph
has an affine block.

Let g be a valid tuple in an additive commutative group in which doubling
is injective. Suppose f is a partial negative affine doubling map on
S, expressed by

    g(f(i))+2*g(i)=t  for every i in S.

If f(i) also lies in S, applying the equation twice gives

    g(f(f(i)))+g(f(i))=2*g(i).

Pair-sum rigidity and injective doubling force f(i)=i. Conversely a
fixed point in S plainly maps into S. Thus a nonfixed image cannot stay
in the domain.

The map is injective on S: equal images cancel in the defining equation,
and then doubling injectivity and tuple injectivity identify their
preimages. Consequently the nonfixed part of S injects into the
complement of S. If F={i in S : f(i)=i}, then

    2*|S| <= n+|F|.

The fixed-point term is explicit. Fixed points satisfy 3*g(i)=t, but no
bound on their number is asserted here. In particular this file does
not silently rule out negative affine blocks when investigating dense
represented differences. Extraction of a large positive or negative
block from pair density remains unproved. The generic central bounds
and G1/G2/G3 remain open.

All three original proof bodies pass both Mathlib revisions. Six exact
declaration types and the ValidTuple definition value agree; the axiom
audit finds only standard Lean axioms. No new definition is introduced.
Split Prove2Me export and publication remain.

## Verified three-theorem negative affine export

All three negative affine statements and original proof bodies have a
verified split export on both revisions. Three exact target types and
dependency sets, two external interface types, one original inline
helper type and the ValidTuple definition value agree. No new definition
bundle is introduced. Metadata and live preflight pass; publication is
pending. The domain bound keeps its fixed-point term explicit. Extracting
affine structure from pair density, absolute central counts and generic
G1/G2/G3 remain open.
