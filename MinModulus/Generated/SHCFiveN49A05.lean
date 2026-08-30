import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_05 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 3785, 2485, 3765, 642, 643, 403, 2786, 402, 2626, 4387, 4232, 589, 2631, 773, 2468, 153, 85, 4234, 4884, 27, 1347, 209, 775, 524, 155, 2306, 2788, 774, 2465, 4425, 2466, 2628, 217, 3746, 401, 3586, 4237, 2633, 641, 321, 837, 20, 4547, 4552, 713, 4397, 1988, 10, 4224, 2478, 4707, 2305, 771, 31, 4385, 1905, 4265, 5191, 2808, 4225, 1528, 770, 465, 705, 2944, 2546, 12, 22, 30, 385, 25]

private theorem valid49_05 : ∀ code ∈ codes49_05, validRelationCode code := by
  decide

private theorem cover49_05 : ∀ q : IncreasingFourTail 47 (⟨5, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_05 (increasingFourValues (N := 49) ⟨⟨5, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a05
    (q : IncreasingFourTail 47 (⟨5, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨5, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_05 _ valid49_05 (cover49_05 q)

end MinModulus.SHCFiveCertificate.Generated
