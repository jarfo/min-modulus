import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 19,600 increasing normalized tails with first entry 5. -/
theorem all_covered_row_5 : coveredRow 5=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
