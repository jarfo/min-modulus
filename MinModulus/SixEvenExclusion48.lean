import MinModulus.SixEvenCertificate48

namespace MinModulus
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_validTuple_six_mod_48 (g : Fin 6 → ZMod 48) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 48) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_two_quotient_sorted_exclusion (N := 48) (p := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (SixEvenCertificate.not_validTuple_sorted 48
      SixEvenCertificate.N48.rivals SixEvenCertificate.N48.all_covered) g


end MinModulus
