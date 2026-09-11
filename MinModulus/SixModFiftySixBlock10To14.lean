import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of every increasing tail whose first entry is in [10,14). -/
theorem all_covered_10_14 : coveredBlock 10 14=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
