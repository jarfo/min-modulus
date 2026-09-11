import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 23,426 increasing normalized tails with first entry 2. -/
theorem all_covered_row_2 : coveredRow 2=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
