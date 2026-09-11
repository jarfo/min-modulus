import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 6,545 increasing normalized tails with first entry 20. -/
theorem all_covered_row_20 : coveredRow 20=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
