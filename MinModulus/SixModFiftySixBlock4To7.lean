import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of every increasing tail whose first entry is in [4,7). -/
theorem all_covered_4_7 : coveredBlock 4 7=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
