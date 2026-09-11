import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 15,180 increasing normalized tails with first entry 9. -/
theorem all_covered_row_9 : coveredRow 9=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
