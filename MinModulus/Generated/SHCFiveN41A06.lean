import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_06 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 2308, 263, 772, 4227, 1825, 3765, 209, 713, 321, 642, 402, 2626, 1665, 1905, 4425, 2465, 4234, 4884, 643, 154, 773, 2468, 26, 153, 4232, 2064, 4387, 20, 524, 10, 641, 85, 21, 2306, 518, 589, 2624, 3785, 401, 2485, 2631, 4584, 3586, 12, 89, 898, 278, 13, 24, 774, 14, 217, 25, 525]

private theorem valid41_06 : ∀ code ∈ codes41_06, validRelationCode code := by
  decide

private theorem cover41_06 : ∀ q : IncreasingFourTail 39 (⟨6, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_06 (increasingFourValues (N := 41) ⟨⟨6, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a06
    (q : IncreasingFourTail 39 (⟨6, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨6, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_06 _ valid41_06 (cover41_06 q)

end MinModulus.SHCFiveCertificate.Generated
