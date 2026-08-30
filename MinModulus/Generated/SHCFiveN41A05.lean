import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_05 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 3765, 642, 643, 402, 403, 2786, 2626, 85, 589, 2631, 4387, 4232, 153, 773, 2468, 209, 27, 713, 1905, 4425, 2465, 321, 13, 10, 4234, 2305, 1528, 4265, 1993, 89, 155, 2485, 20, 12, 641, 2466, 1828, 2633, 24, 4544]

private theorem valid41_05 : ∀ code ∈ codes41_05, validRelationCode code := by
  decide

private theorem cover41_05 : ∀ q : IncreasingFourTail 39 (⟨5, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_05 (increasingFourValues (N := 41) ⟨⟨5, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a05
    (q : IncreasingFourTail 39 (⟨5, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨5, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_05 _ valid41_05 (cover41_05 q)

end MinModulus.SHCFiveCertificate.Generated
