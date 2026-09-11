import MinModulus.SixModFortyTwoConditional
import MinModulus.SixModFortyTwoUnitCertificate
import MinModulus.SixModFortyTwoNonunitCertificate

namespace MinModulus

theorem not_validTuple_six_mod_forty_two (g : Fin 6 → ZMod 42) : ¬ ValidTuple g :=
  not_validTuple_six_mod_forty_two_of_certificates
    SixFortyTwoCertificate.all_unit_covered SixFortyTwoCertificate.all_nonunit_covered g


end MinModulus
