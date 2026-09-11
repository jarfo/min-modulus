import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of every increasing tail whose first entry is in [28,56). -/
theorem all_covered_28_56 : coveredBlock 28 56=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
