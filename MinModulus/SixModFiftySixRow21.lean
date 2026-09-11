import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 5,984 increasing normalized tails with first entry 21. -/
theorem all_covered_row_21 : coveredRow 21=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
