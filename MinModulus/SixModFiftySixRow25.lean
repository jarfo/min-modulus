import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 4,060 increasing normalized tails with first entry 25. -/
theorem all_covered_row_25 : coveredRow 25=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
