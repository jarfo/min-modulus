import MinModulus.SixEvenCertificate40

namespace MinModulus
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem not_validTuple_six_mod_40 (g : Fin 6 → ZMod 40) : ¬ ValidTuple g := by
  letI : Nontrivial (ZMod 40) := ⟨⟨0,1,by decide⟩⟩
  exact not_validTuple_six_of_two_quotient_sorted_exclusion (N := 40) (p := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (SixEvenCertificate.not_validTuple_sorted 40
      SixEvenCertificate.N40.rivals SixEvenCertificate.N40.all_covered) g


end MinModulus
