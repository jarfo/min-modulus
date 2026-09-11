import MinModulus.SixModFiftySixRow2
import MinModulus.SixModFiftySixRow3

namespace MinModulus.SixModFiftySixCertificate

private theorem combine_rows (a b : Bool) (ha : a=true) (hb : b=true) : (a && b)=true := by
  cases ha
  cases hb
  rfl

/-- The individually checked rows cover the interval [2,4). -/
theorem all_covered_2_4 : coveredBlock 2 4=true :=
  (combine_rows (coveredRow 2) (coveredRow 3 && (true)) all_covered_row_2 (combine_rows (coveredRow 3) (true) all_covered_row_3 (rfl : true=true)))

end MinModulus.SixModFiftySixCertificate
