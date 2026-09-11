import MinModulus.SixEvenCertificate44

namespace MinModulus
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_validTuple_six_mod_44 (g : Fin 6 → ZMod 44) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 44) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_two_quotient_sorted_exclusion (N := 44) (p := 11)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (SixEvenCertificate.not_validTuple_sorted 44
      SixEvenCertificate.N44.rivals SixEvenCertificate.N44.all_covered) g


end MinModulus
