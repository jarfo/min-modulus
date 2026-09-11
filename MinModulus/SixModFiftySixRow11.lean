import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 13,244 increasing normalized tails with first entry 11. -/
theorem all_covered_row_11 : coveredRow 11=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
