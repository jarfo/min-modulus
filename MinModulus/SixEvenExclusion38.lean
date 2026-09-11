import MinModulus.SixEvenCertificate38

namespace MinModulus
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_validTuple_six_mod_38 (g : Fin 6 → ZMod 38) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 38) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_two_quotient_sorted_exclusion (N := 38) (p := 19)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (SixEvenCertificate.not_validTuple_sorted 38
      SixEvenCertificate.N38.rivals SixEvenCertificate.N38.all_covered) g


end MinModulus
