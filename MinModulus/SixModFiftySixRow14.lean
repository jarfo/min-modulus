import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 10,660 increasing normalized tails with first entry 14. -/
theorem all_covered_row_14 : coveredRow 14=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
