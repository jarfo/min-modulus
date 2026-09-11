import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 3,654 increasing normalized tails with first entry 26. -/
theorem all_covered_row_26 : coveredRow 26=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
