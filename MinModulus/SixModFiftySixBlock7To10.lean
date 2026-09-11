import MinModulus.SixModFiftySixRow7
import MinModulus.SixModFiftySixRow8
import MinModulus.SixModFiftySixRow9

namespace MinModulus.SixModFiftySixCertificate

private theorem combine_rows (a b : Bool) (ha : a=true) (hb : b=true) : (a && b)=true := by
  cases ha
  cases hb
  rfl

/-- The individually checked rows cover the interval [7,10). -/
theorem all_covered_7_10 : coveredBlock 7 10=true :=
  (combine_rows (coveredRow 7) (coveredRow 8 && (coveredRow 9 && (true))) all_covered_row_7 (combine_rows (coveredRow 8) (coveredRow 9 && (true)) all_covered_row_8 (combine_rows (coveredRow 9) (true) all_covered_row_9 (rfl : true=true))))

end MinModulus.SixModFiftySixCertificate
