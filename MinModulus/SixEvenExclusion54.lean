import MinModulus.SixEvenCertificate54

namespace MinModulus
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_validTuple_six_mod_54 (g : Fin 6 → ZMod 54) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 54) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_two_quotient_sorted_exclusion (N := 54) (p := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (SixEvenCertificate.not_validTuple_sorted 54
      SixEvenCertificate.N54.rivals SixEvenCertificate.N54.all_covered) g


end MinModulus
