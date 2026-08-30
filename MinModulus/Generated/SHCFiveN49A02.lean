import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_02 : List ℕ := [17, 521, 261, 131, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1825, 3785, 2485, 1665, 4227, 1187, 1507, 2306, 524, 772, 2308, 20, 2633, 2468, 4884, 773, 217, 153, 589, 5204, 85, 2631, 837, 2478, 775, 774, 154, 2466, 642, 401, 402, 465, 3344, 3024, 403, 3185, 5045, 525, 21, 526, 527, 155, 4544, 2476, 705, 4224, 22, 643, 961, 641, 2488, 12, 385, 25, 29, 77, 93, 897, 24, 28, 26, 449, 769, 898, 833, 89, 23, 31, 5824]

private theorem valid49_02 : ∀ code ∈ codes49_02, validRelationCode code := by
  decide

private theorem cover49_02 : ∀ q : IncreasingFourTail 47 (⟨2, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_02 (increasingFourValues (N := 49) ⟨⟨2, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a02
    (q : IncreasingFourTail 47 (⟨2, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨2, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_02 _ valid49_02 (cover49_02 q)

end MinModulus.SHCFiveCertificate.Generated
