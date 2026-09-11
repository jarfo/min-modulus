import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 7,770 increasing normalized tails with first entry 18. -/
theorem all_covered_row_18 : coveredRow 18=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
