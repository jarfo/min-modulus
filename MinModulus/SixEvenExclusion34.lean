import MinModulus.SixEvenCertificate34

namespace MinModulus
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_validTuple_six_mod_34 (g : Fin 6 → ZMod 34) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 34) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_two_quotient_sorted_exclusion (N := 34) (p := 17)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (SixEvenCertificate.not_validTuple_sorted 34
      SixEvenCertificate.N34.rivals SixEvenCertificate.N34.all_covered) g


end MinModulus
