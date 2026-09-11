import MinModulus.SixEvenCertificate46

namespace MinModulus
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_validTuple_six_mod_46 (g : Fin 6 → ZMod 46) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 46) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_two_quotient_sorted_exclusion (N := 46) (p := 23)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (SixEvenCertificate.not_validTuple_sorted 46
      SixEvenCertificate.N46.rivals SixEvenCertificate.N46.all_covered) g


end MinModulus
