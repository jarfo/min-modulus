import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 8,436 increasing normalized tails with first entry 17. -/
theorem all_covered_row_17 : coveredRow 17=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
