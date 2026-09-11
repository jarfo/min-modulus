import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 16,215 increasing normalized tails with first entry 8. -/
theorem all_covered_row_8 : coveredRow 8=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
