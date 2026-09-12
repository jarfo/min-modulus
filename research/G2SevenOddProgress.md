# Seven-coordinate odd-modulus proof progress

The general complementary-coin theorem proves N>=107 for a valid
seven-tuple at odd order. The ten possible moduli below 127 are handled
by separate unconditional Lean exclusions. Each completed exclusion is
checked on both Lean revisions, with literal theorem-type comparisons,
standard-axiom audits, and matching values for the seven core definitions.

| Modulus | Local Lean status | Source |
| --- | --- | --- |
| 107 | Verified on both revisions | [G2Seven107.lean](../MinModulus/G2Seven107.lean) |
| 109 | Pending | |
| 111 | Pending | |
| 113 | Pending | |
| 115 | Pending | |
| 117 | Pending | |
| 119 | Pending | |
| 121 | Pending | |
| 123 | Pending | |
| 125 | Pending | |

These modules are not yet imported by the default library root. They can
be built explicitly with `lake build MinModulus.G2SevenN`, replacing N
by a completed modulus. The final dimension-seven bridge is still pending.
G1, G2, G3 and the full min-modulus conjecture remain open.
