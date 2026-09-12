# Seven-coordinate odd-modulus proof progress

The general complementary-coin theorem proves N>=107 for a valid
seven-tuple at odd order. The ten possible moduli below 127 are handled
by separate unconditional Lean exclusions. Each completed exclusion is
checked on both Lean revisions, with literal theorem-type comparisons,
standard-axiom audits, and matching values for the seven core definitions.

| Modulus | Local Lean status | Source |
| --- | --- | --- |
| 107 | Verified on both revisions | [G2Seven107.lean](../MinModulus/G2Seven107.lean) |
| 109 | Verified on both revisions | [G2Seven109.lean](../MinModulus/G2Seven109.lean) |
| 111 | Verified on both revisions | [G2Seven111.lean](../MinModulus/G2Seven111.lean) |
| 113 | Verified on both revisions | [G2Seven113.lean](../MinModulus/G2Seven113.lean) |
| 115 | Verified on both revisions | [G2Seven115.lean](../MinModulus/G2Seven115.lean) |
| 117 | Verified on both revisions | [G2Seven117.lean](../MinModulus/G2Seven117.lean) |
| 119 | Verified on both revisions | [G2Seven119.lean](../MinModulus/G2Seven119.lean) |
| 121 | Verified on both revisions | [G2Seven121.lean](../MinModulus/G2Seven121.lean) |
| 123 | Verified on both revisions | [G2Seven123.lean](../MinModulus/G2Seven123.lean) |
| 125 | Verified on both revisions | [G2Seven125.lean](../MinModulus/G2Seven125.lean) |

The [dimension-seven bridge](../MinModulus/G2OddSevenDimensions.lean) is now verified on both revisions
and imported by the default library root. It proves the sharp bound N>=127
and the equivalence of full G2 with its restriction to n>=8. Integration
checks compile the root against previously audited dependency objects and
run the required axiom and certificate-import checks; no clean full rebuild
was run for this integration milestone.

This is a local theorem result. Prove2Me still has G2/From7 as its open
frontier until the connecting proofs are accepted there. G1, general G2,
G3 and the full conjecture remain open. Further proof work prioritizes a
generic-n argument, starting with half-degree coin growth.
