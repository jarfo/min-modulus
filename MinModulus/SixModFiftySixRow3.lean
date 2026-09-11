import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 22,100 increasing normalized tails with first entry 3. -/
theorem all_covered_row_3 : coveredRow 3=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
