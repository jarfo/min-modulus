import MinModulus.SixEvenCertificate52

namespace MinModulus
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_validTuple_six_mod_52 (g : Fin 6 → ZMod 52) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 52) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_two_quotient_sorted_exclusion (N := 52) (p := 13)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (SixEvenCertificate.not_validTuple_sorted 52
      SixEvenCertificate.N52.rivals SixEvenCertificate.N52.all_covered) g


end MinModulus
