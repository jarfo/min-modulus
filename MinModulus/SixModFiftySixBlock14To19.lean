import MinModulus.SixModFiftySixRow14
import MinModulus.SixModFiftySixRow15
import MinModulus.SixModFiftySixRow16
import MinModulus.SixModFiftySixRow17
import MinModulus.SixModFiftySixRow18

namespace MinModulus.SixModFiftySixCertificate

private theorem combine_rows (a b : Bool) (ha : a=true) (hb : b=true) : (a && b)=true := by
  cases ha
  cases hb
  rfl

/-- The individually checked rows cover the interval [14,19). -/
theorem all_covered_14_19 : coveredBlock 14 19=true :=
  (combine_rows (coveredRow 14) (coveredRow 15 && (coveredRow 16 && (coveredRow 17 && (coveredRow 18 && (true))))) all_covered_row_14 (combine_rows (coveredRow 15) (coveredRow 16 && (coveredRow 17 && (coveredRow 18 && (true)))) all_covered_row_15 (combine_rows (coveredRow 16) (coveredRow 17 && (coveredRow 18 && (true))) all_covered_row_16 (combine_rows (coveredRow 17) (coveredRow 18 && (true)) all_covered_row_17 (combine_rows (coveredRow 18) (true) all_covered_row_18 (rfl : true=true))))))

end MinModulus.SixModFiftySixCertificate
