import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 9,880 increasing normalized tails with first entry 15. -/
theorem all_covered_row_15 : coveredRow 15=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
