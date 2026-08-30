import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_03 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 524, 2306, 20, 642, 402, 2626, 643, 403, 2786, 1347, 2631, 85, 589, 21, 1187, 401, 385, 641, 2466, 4547, 4237, 2628, 774, 525, 154, 773, 3344, 153, 3185, 2546, 526, 465, 3586, 3746, 2476, 386, 4385, 4544, 4224, 2148, 775, 2788, 4225, 4230, 1993, 387, 4387, 1837, 770, 705, 837, 3105, 5665, 2706, 217, 3024, 5510, 4707, 898, 4865, 5186, 24, 30, 897, 1827, 26, 22, 93, 25, 2944, 2945, 4885, 1586, 4866]

private theorem valid49_03 : ∀ code ∈ codes49_03, validRelationCode code := by
  decide

private theorem cover49_03 : ∀ q : IncreasingFourTail 47 (⟨3, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_03 (increasingFourValues (N := 49) ⟨⟨3, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a03
    (q : IncreasingFourTail 47 (⟨3, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨3, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_03 _ valid49_03 (cover49_03 q)

end MinModulus.SHCFiveCertificate.Generated
