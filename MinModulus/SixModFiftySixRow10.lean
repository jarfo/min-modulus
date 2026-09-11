import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 14,190 increasing normalized tails with first entry 10. -/
theorem all_covered_row_10 : coveredRow 10=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
