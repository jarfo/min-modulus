import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_04 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 642, 402, 2626, 524, 2306, 20, 403, 2786, 643, 85, 589, 153, 2631, 773, 2468, 4232, 2466, 401, 641, 4387, 3765, 21, 525, 4234, 4385, 775, 4224, 155, 3185, 4547, 2546, 2788, 217, 774, 4225, 4237, 2628, 2633, 321, 154, 837, 2305, 25, 4230, 3912, 4544, 1186, 1827, 385, 387, 465, 705, 4265, 2866, 4707, 770, 386, 526, 449, 769, 4884, 1586, 5191, 27, 3946, 2648, 22, 30, 833]

private theorem valid49_04 : ∀ code ∈ codes49_04, validRelationCode code := by
  decide

private theorem cover49_04 : ∀ q : IncreasingFourTail 47 (⟨4, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_04 (increasingFourValues (N := 49) ⟨⟨4, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a04
    (q : IncreasingFourTail 47 (⟨4, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨4, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_04 _ valid49_04 (cover49_04 q)

end MinModulus.SHCFiveCertificate.Generated
