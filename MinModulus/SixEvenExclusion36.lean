import MinModulus.SixEvenCertificate36

namespace MinModulus
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_validTuple_six_mod_36 (g : Fin 6 → ZMod 36) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 36) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_two_quotient_sorted_exclusion (N := 36) (p := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (SixEvenCertificate.not_validTuple_sorted 36
      SixEvenCertificate.N36.rivals SixEvenCertificate.N36.all_covered) g


end MinModulus
