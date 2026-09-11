import MinModulus.SixModFiftySixRow10
import MinModulus.SixModFiftySixRow11
import MinModulus.SixModFiftySixRow12
import MinModulus.SixModFiftySixRow13

namespace MinModulus.SixModFiftySixCertificate

private theorem combine_rows (a b : Bool) (ha : a=true) (hb : b=true) : (a && b)=true := by
  cases ha
  cases hb
  rfl

/-- The individually checked rows cover the interval [10,14). -/
theorem all_covered_10_14 : coveredBlock 10 14=true :=
  (combine_rows (coveredRow 10) (coveredRow 11 && (coveredRow 12 && (coveredRow 13 && (true)))) all_covered_row_10 (combine_rows (coveredRow 11) (coveredRow 12 && (coveredRow 13 && (true))) all_covered_row_11 (combine_rows (coveredRow 12) (coveredRow 13 && (true)) all_covered_row_12 (combine_rows (coveredRow 13) (true) all_covered_row_13 (rfl : true=true)))))

end MinModulus.SixModFiftySixCertificate
