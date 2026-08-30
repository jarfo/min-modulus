import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_03 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 524, 2306, 20, 642, 402, 2626, 403, 2786, 643, 21, 641, 85, 401, 3765, 2466, 589, 525, 2631, 385, 2546, 386, 465, 3746, 1186, 4224, 5025, 4225, 3906, 4387, 449, 3786, 22, 2788, 705, 3024, 154, 526, 899, 387, 153, 773, 775]

private theorem valid41_03 : ∀ code ∈ codes41_03, validRelationCode code := by
  decide

private theorem cover41_03 : ∀ q : IncreasingFourTail 39 (⟨3, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_03 (increasingFourValues (N := 41) ⟨⟨3, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a03
    (q : IncreasingFourTail 39 (⟨3, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨3, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_03 _ valid41_03 (cover41_03 q)

end MinModulus.SHCFiveCertificate.Generated
