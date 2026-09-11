import MinModulus.SixEvenCertificate50

namespace MinModulus
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_validTuple_six_mod_50 (g : Fin 6 → ZMod 50) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 50) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_two_quotient_sorted_exclusion (N := 50) (p := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (SixEvenCertificate.not_validTuple_sorted 50
      SixEvenCertificate.N50.rivals SixEvenCertificate.N50.all_covered) g


end MinModulus
