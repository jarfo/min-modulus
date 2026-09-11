import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 9,139 increasing normalized tails with first entry 16. -/
theorem all_covered_row_16 : coveredRow 16=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
