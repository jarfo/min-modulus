import MinModulus.SixModFiftySixRow4
import MinModulus.SixModFiftySixRow5
import MinModulus.SixModFiftySixRow6

namespace MinModulus.SixModFiftySixCertificate

private theorem combine_rows (a b : Bool) (ha : a=true) (hb : b=true) : (a && b)=true := by
  cases ha
  cases hb
  rfl

/-- The individually checked rows cover the interval [4,7). -/
theorem all_covered_4_7 : coveredBlock 4 7=true :=
  (combine_rows (coveredRow 4) (coveredRow 5 && (coveredRow 6 && (true))) all_covered_row_4 (combine_rows (coveredRow 5) (coveredRow 6 && (true)) all_covered_row_5 (combine_rows (coveredRow 6) (true) all_covered_row_6 (rfl : true=true))))

end MinModulus.SixModFiftySixCertificate
