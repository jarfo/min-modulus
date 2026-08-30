import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_02 : List ℕ := [17, 521, 261, 131, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1825, 3785, 2485, 1665, 4227, 1187, 2306, 1507, 524, 772, 4884, 2308, 20, 2468, 2633, 773, 217, 153, 589, 5204, 2631, 837, 85, 4397, 465, 775, 2476, 2478, 705, 4552, 21, 1828, 13, 3024, 1527, 1868, 774, 23, 24, 642, 31]

private theorem valid41_02 : ∀ code ∈ codes41_02, validRelationCode code := by
  decide

private theorem cover41_02 : ∀ q : IncreasingFourTail 39 (⟨2, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_02 (increasingFourValues (N := 41) ⟨⟨2, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a02
    (q : IncreasingFourTail 39 (⟨2, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨2, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_02 _ valid41_02 (cover41_02 q)

end MinModulus.SHCFiveCertificate.Generated
