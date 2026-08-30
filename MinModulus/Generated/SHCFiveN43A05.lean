import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_05 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 3765, 642, 643, 403, 2786, 402, 2626, 85, 589, 2631, 4387, 4232, 153, 773, 2468, 4234, 27, 209, 713, 4425, 2465, 2485, 3746, 2306, 524, 3586, 2466, 2546, 1905, 321, 3785, 4865, 10, 20, 21, 12, 641, 526, 385, 401, 89, 897, 525, 2944, 4224, 3911, 1907, 30]

private theorem valid43_05 : ∀ code ∈ codes43_05, validRelationCode code := by
  decide

private theorem cover43_05 : ∀ q : IncreasingFourTail 41 (⟨5, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_05 (increasingFourValues (N := 43) ⟨⟨5, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a05
    (q : IncreasingFourTail 41 (⟨5, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨5, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_05 _ valid43_05 (cover43_05 q)

end MinModulus.SHCFiveCertificate.Generated
