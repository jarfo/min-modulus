# The large-dimension strength of TwoEscapeShift

The parallel `TwoEscapeShift` proposal has a consequence beyond G1.
The repository already proves that every valid tuple strictly below its
stratum bound, in dimension at least 52, has at least three affine-doubling
escapes at every shift. The proposed extraction gives a shift with at
most two escapes in that same critical even-stratum range. Combining
these statements rules out every such tuple directly.

[TwoEscapeLargeBound.lean](TwoEscapeLargeBound.lean) proves six implications:

* `TwoEscapeShift` gives the exact even-stratum bound for every n>=52.
* It gives the global bound at every positive even modulus for n>=52.
* With G2, it gives the global bound at every positive modulus for n>=52,
  without a G3 premise or an induction through smaller dimensions.
* It gives the full exceptional-lift obstruction for n>=52.
* With the exceptional exclusions for 2<=n<52, it gives full G3.
* With G2 and those bounded exceptional exclusions, it gives the full
  arbitrary-n global bound through the existing deletion assembly.

For the G3 step, a non-power-of-two n has

    2*globalBound(n-1) < globalBound(n).

The exceptional modulus is positive and even. Thus the second implication
excludes it immediately; neither the odd-base hypothesis nor any
classification of extremal tuples is needed for this conditional result.

## Scope

Every implication assumes `TwoEscapeShift`; that predicate is still
unproved. In dimensions at least 52 its critical-instance condition
would hold only because there are no critical even-stratum tuples.
It therefore carries more of the global conjecture than the original
G1-only description suggests. No converse with the full G1 gate is claimed.

The bounded G3 premise is explicit and unproved here. Existing small
exclusions may discharge some of its instances, but this file performs
no finite search and starts no enumeration campaign. The main priority
remains a generic proof of an open input. The server's three original
open leaves are unchanged; these implications do not close G1, G2 or G3.

## Verification

All six implications compile on the repository's original Lean 4.32.0
revision. The audit records sixteen declaration types and seven exact
definition values, and verifies that only standard axioms occur.
Existing audited dependency objects were reused, including the parallel
G1 extraction interface and the unconditional three-escape theorem.
There is no additional axiom and no proof hole in this source.

The supported Lean 4.33.1 port has not been checked for these implications;
their deeper escape-bound dependencies are not in the current small
supported port. No platform theorem or proof is uploaded for this file.
This is separate from the four accepted G3 balanced-kernel statements,
which were built and audited on both revisions.
