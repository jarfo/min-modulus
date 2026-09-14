# Dense positive-domain proof chain

For a valid tuple of length n>=144 at odd modulus N, let D be a family
of two-coordinate subsets covering every unrepresented doubled coordinate
difference. If (n-9)*|D|<3*choose(n,2), then 2^n-1<=N. The density
premise is explicit. The proof obtains a large full positive affine
domain, bounds its complement by one, and applies AlmostDoubling.

Any remaining odd counterexample at n>=144 must satisfy
3*choose(n,2)<=(n-9)*|D| for every such pair cover. This argument does
not cover n<144; existing small-dimension results remain valid. The sparse
represented-pair regime, absolute central inequalities and unrestricted
G1/G2/G3 remain open.

The fourteen original proofs are in five source modules:

* FullPositiveDomainNeighbors.lean: four domain-map and neighbor bounds.
* CrossPairDeficit.lean: two incidence and averaging bounds.
* DenseDomainComplementArithmetic.lean: three scalar density implications.
* DensePositiveDomainOneEscape.lean: three actual one-escape extraction results.
* DensePairModulusBound.lean: the sharp odd bound and necessary counterexample density.

The split export passes both revisions: fourteen exact original target
types and dependency sets, four external interface types, one original
inline helper type and two existing definition values match. All original
proof bodies are retained. No new definition bundle is introduced. Five
files use restricted parser spans; the OddOrder helper uses full compiler
InfoTree spans because its source has section variables. Metadata and live
preflight pass. Private proof publication is pending.
