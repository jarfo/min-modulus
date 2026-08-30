import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_06 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 402, 642, 2626, 403, 643, 2786, 153, 773, 4387, 4232, 2468, 589, 85, 2631, 4234, 3765, 4884, 321, 3785, 2485, 2305, 26, 2064, 4265, 209, 518, 713, 401, 385, 2306, 524, 10, 641, 4425, 2465, 3586, 1905, 2546, 774, 4870, 2466, 2628, 4237, 2788, 525, 2624, 20, 775, 12, 465, 4547, 2148, 3185, 3746, 1828, 3118, 21, 2808, 154, 771, 11, 4584, 2478, 770, 278, 217, 837, 3264, 1507, 24, 14, 769, 29, 527, 4866]

private theorem valid49_06 : ∀ code ∈ codes49_06, validRelationCode code := by
  decide

private theorem cover49_06 : ∀ q : IncreasingFourTail 47 (⟨6, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_06 (increasingFourValues (N := 49) ⟨⟨6, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a06
    (q : IncreasingFourTail 47 (⟨6, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨6, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_06 _ valid49_06 (cover49_06 q)

end MinModulus.SHCFiveCertificate.Generated
