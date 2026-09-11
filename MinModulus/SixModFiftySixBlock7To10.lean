import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of every increasing tail whose first entry is in [7,10). -/
theorem all_covered_7_10 : coveredBlock 7 10=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
