import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of the 20,825 increasing normalized tails with first entry 4. -/
theorem all_covered_row_4 : coveredRow 4=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
