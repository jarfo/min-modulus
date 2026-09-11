import MinModulus.SortedValidTuples
import MinModulus.SixModFortyTwoData

namespace MinModulus

theorem not_validTuple_six_mod_forty_two_of_certificates
    (hunit : SixFortyTwoCertificate.unitBlock 2 42=true)
    (hnonunit : SixFortyTwoCertificate.nonunitBlock 1 42=true)
    (g : Fin 6 → ZMod 42) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 42) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_unit_and_nonunit_exclusions (by decide)
    (SixFortyTwoCertificate.not_validTuple_unit_sorted hunit)
    (SixFortyTwoCertificate.not_validTuple_nonunit_sorted hnonunit) g


end MinModulus
