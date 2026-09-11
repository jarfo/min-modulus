import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of every increasing tail whose first entry is in [2,4). -/
theorem all_covered_2_4 : coveredBlock 2 4=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
