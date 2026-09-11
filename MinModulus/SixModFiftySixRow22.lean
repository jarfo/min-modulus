import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 5,456 increasing normalized tails with first entry 22. -/
theorem all_covered_row_22 : coveredRow 22=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
