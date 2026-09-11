import MinModulus.SixModFiftySixRow19
import MinModulus.SixModFiftySixRow20
import MinModulus.SixModFiftySixRow21
import MinModulus.SixModFiftySixRow22
import MinModulus.SixModFiftySixRow23
import MinModulus.SixModFiftySixRow24
import MinModulus.SixModFiftySixRow25
import MinModulus.SixModFiftySixRow26
import MinModulus.SixModFiftySixRow27

namespace MinModulus.SixModFiftySixCertificate

private theorem combine_rows (a b : Bool) (ha : a=true) (hb : b=true) : (a && b)=true := by
  cases ha
  cases hb
  rfl

/-- The individually checked rows cover the interval [19,28). -/
theorem all_covered_19_28 : coveredBlock 19 28=true :=
  (combine_rows (coveredRow 19) (coveredRow 20 && (coveredRow 21 && (coveredRow 22 && (coveredRow 23 && (coveredRow 24 && (coveredRow 25 && (coveredRow 26 && (coveredRow 27 && (true))))))))) all_covered_row_19 (combine_rows (coveredRow 20) (coveredRow 21 && (coveredRow 22 && (coveredRow 23 && (coveredRow 24 && (coveredRow 25 && (coveredRow 26 && (coveredRow 27 && (true)))))))) all_covered_row_20 (combine_rows (coveredRow 21) (coveredRow 22 && (coveredRow 23 && (coveredRow 24 && (coveredRow 25 && (coveredRow 26 && (coveredRow 27 && (true))))))) all_covered_row_21 (combine_rows (coveredRow 22) (coveredRow 23 && (coveredRow 24 && (coveredRow 25 && (coveredRow 26 && (coveredRow 27 && (true)))))) all_covered_row_22 (combine_rows (coveredRow 23) (coveredRow 24 && (coveredRow 25 && (coveredRow 26 && (coveredRow 27 && (true))))) all_covered_row_23 (combine_rows (coveredRow 24) (coveredRow 25 && (coveredRow 26 && (coveredRow 27 && (true)))) all_covered_row_24 (combine_rows (coveredRow 25) (coveredRow 26 && (coveredRow 27 && (true))) all_covered_row_25 (combine_rows (coveredRow 26) (coveredRow 27 && (true)) all_covered_row_26 (combine_rows (coveredRow 27) (true) all_covered_row_27 (rfl : true=true))))))))))

end MinModulus.SixModFiftySixCertificate
