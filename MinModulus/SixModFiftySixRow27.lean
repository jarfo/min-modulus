import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 3,276 increasing normalized tails with first entry 27. -/
theorem all_covered_row_27 : coveredRow 27=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
