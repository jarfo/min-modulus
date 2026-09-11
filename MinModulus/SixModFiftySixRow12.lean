import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 12,341 increasing normalized tails with first entry 12. -/
theorem all_covered_row_12 : coveredRow 12=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
