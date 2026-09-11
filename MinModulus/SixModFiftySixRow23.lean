import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 4,960 increasing normalized tails with first entry 23. -/
theorem all_covered_row_23 : coveredRow 23=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
