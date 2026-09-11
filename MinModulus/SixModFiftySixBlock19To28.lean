import MinModulus.SixModFiftySixData

namespace MinModulus.SixModFiftySixCertificate

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Kernel verification of every increasing tail whose first entry is in [19,28). -/
theorem all_covered_19_28 : coveredBlock 19 28=true := by decide +kernel

end MinModulus.SixModFiftySixCertificate
