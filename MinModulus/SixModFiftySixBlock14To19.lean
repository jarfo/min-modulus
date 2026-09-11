import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of every increasing tail whose first entry is in [14,19). -/
theorem all_covered_14_19 : coveredBlock 14 19=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
