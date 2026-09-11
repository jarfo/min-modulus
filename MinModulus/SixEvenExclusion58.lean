import MinModulus.SixEvenCertificate58

namespace MinModulus
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_validTuple_six_mod_58 (g : Fin 6 → ZMod 58) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 58) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_two_quotient_sorted_exclusion (N := 58) (p := 29)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (SixEvenCertificate.not_validTuple_sorted 58
      SixEvenCertificate.N58.rivals SixEvenCertificate.N58.all_covered) g


end MinModulus
