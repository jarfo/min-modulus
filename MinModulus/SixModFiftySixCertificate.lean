import MinModulus.SixModFiftySixBlock2To4
import MinModulus.SixModFiftySixBlock4To7
import MinModulus.SixModFiftySixBlock7To10
import MinModulus.SixModFiftySixBlock10To14
import MinModulus.SixModFiftySixBlock14To19
import MinModulus.SixModFiftySixBlock19To28
import MinModulus.SixModFiftySixBlock28To56

namespace MinModulus.SixModFiftySixCertificate

/-- The bounded checks imply the complete original normalized-tail check. -/
theorem all_covered_of_blocks
    (h2_4 : coveredBlock 2 4=true)
    (h4_7 : coveredBlock 4 7=true)
    (h7_10 : coveredBlock 7 10=true)
    (h10_14 : coveredBlock 10 14=true)
    (h14_19 : coveredBlock 14 19=true)
    (h19_28 : coveredBlock 19 28=true)
    (h28_56 : coveredBlock 28 56=true)
    : ((List.range 54).all fun x ↦
      let a := x+2
      (List.range (55-a)).all fun y ↦
        let b := a+1+y
        (List.range (55-b)).all fun z ↦
          let c := b+1+z
          (List.range (55-c)).all fun t ↦
            covered a b c (c+1+t)) = true := by
  change ((List.range 54).all fun x ↦ coveredRow (x+2))=true
  rw [List.all_eq_true]
  intro x hx
  have hx := List.mem_range.mp hx
  by_cases hlt4 : x+2 < 4
  · exact coveredRow_of_block 2 4 (x+2) h2_4 (by omega) hlt4
  by_cases hlt7 : x+2 < 7
  · exact coveredRow_of_block 4 7 (x+2) h4_7 (by omega) hlt7
  by_cases hlt10 : x+2 < 10
  · exact coveredRow_of_block 7 10 (x+2) h7_10 (by omega) hlt10
  by_cases hlt14 : x+2 < 14
  · exact coveredRow_of_block 10 14 (x+2) h10_14 (by omega) hlt14
  by_cases hlt19 : x+2 < 19
  · exact coveredRow_of_block 14 19 (x+2) h14_19 (by omega) hlt19
  by_cases hlt28 : x+2 < 28
  · exact coveredRow_of_block 19 28 (x+2) h19_28 (by omega) hlt28
  exact coveredRow_of_block 28 56 (x+2) h28_56 (by omega) (by omega)

/-- All 316,251 increasing normalized tails have a checked multiplicity rival.
The seven component computations have no axioms; this assembly uses standard Lean axioms. -/
theorem all_covered :
    ((List.range 54).all fun x ↦
      let a := x+2
      (List.range (55-a)).all fun y ↦
        let b := a+1+y
        (List.range (55-b)).all fun z ↦
          let c := b+1+z
          (List.range (55-c)).all fun t ↦
            covered a b c (c+1+t)) = true :=
  all_covered_of_blocks all_covered_2_4 all_covered_4_7 all_covered_7_10 all_covered_10_14 all_covered_14_19 all_covered_19_28 all_covered_28_56

end MinModulus.SixModFiftySixCertificate
