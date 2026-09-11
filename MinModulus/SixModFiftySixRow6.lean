import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 18,424 increasing normalized tails with first entry 6. -/
theorem all_covered_row_6 : coveredRow 6=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
