import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_03 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 524, 2306, 20, 642, 402, 2626, 1347, 2786, 643, 403, 85, 2631, 589, 21, 641, 401, 2466, 153, 774, 4547, 773, 3185, 154, 525, 3344, 526, 4237, 2628, 4385, 4225, 3025, 775, 386, 4544, 22, 4387, 4230, 4224, 2706, 2468, 4232, 2476, 2788, 465, 385, 2546, 3746, 2148, 4707, 3912, 705, 1993, 3756, 387, 5514, 1186, 3906, 898, 449, 3118, 769, 5505, 1346, 24, 89, 5504, 4870, 3946, 1988, 5191, 1187, 2945, 2950, 770, 527, 4234, 3105, 4865, 3911, 3747, 2808, 1668, 28, 93, 1586]

private theorem valid53_03 : ∀ code ∈ codes53_03, validRelationCode code := by
  decide

private theorem cover53_03 : ∀ q : IncreasingFourTail 51 (⟨3, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_03 (increasingFourValues (N := 53) ⟨⟨3, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a03
    (q : IncreasingFourTail 51 (⟨3, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨3, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_03 _ valid53_03 (cover53_03 q)

end MinModulus.SHCFiveCertificate.Generated
