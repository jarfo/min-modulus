import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 17,296 increasing normalized tails with first entry 7. -/
theorem all_covered_row_7 : coveredRow 7=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
