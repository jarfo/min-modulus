import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_08 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 772, 4227, 2308, 402, 642, 2626, 201, 337, 577, 1825, 403, 643, 2786, 1665, 153, 773, 4387, 4232, 2468, 522, 589, 262, 18, 85, 2631, 4234, 4884, 5184, 523, 2064, 385, 263, 1186, 321, 209, 518, 3586, 1905, 3765, 19, 2624, 4425, 713, 2465, 4265, 2305, 10, 770, 3946, 524, 12, 833]

private theorem valid41_08 : ∀ code ∈ codes41_08, validRelationCode code := by
  decide

private theorem cover41_08 : ∀ q : IncreasingFourTail 39 (⟨8, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_08 (increasingFourValues (N := 41) ⟨⟨8, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a08
    (q : IncreasingFourTail 39 (⟨8, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨8, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_08 _ valid41_08 (cover41_08 q)

end MinModulus.SHCFiveCertificate.Generated
