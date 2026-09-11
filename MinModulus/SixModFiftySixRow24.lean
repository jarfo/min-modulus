import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 4,495 increasing normalized tails with first entry 24. -/
theorem all_covered_row_24 : coveredRow 24=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
