import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_04 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 642, 402, 2626, 524, 2306, 20, 643, 403, 2786, 85, 589, 2631, 773, 2468, 153, 4232, 4387, 401, 2466, 641, 3765, 21, 525, 4385, 3185, 4234, 217, 775, 2628, 4237, 4547, 4224, 4225, 774, 2788, 837, 770, 4230, 2478, 2633, 3025, 154, 705, 321, 1528, 4544, 1993, 2648, 387, 2546, 465, 3344, 3024, 3746, 1667, 385, 4265, 5045, 2305, 3586, 5025, 24, 4865, 1186, 3946, 28, 1508, 386, 449, 1988, 898, 22, 526, 2950, 5186, 77, 769, 4066, 3927, 1868, 1668, 12, 30, 899, 527, 1506]

private theorem valid53_04 : ∀ code ∈ codes53_04, validRelationCode code := by
  decide

private theorem cover53_04 : ∀ q : IncreasingFourTail 51 (⟨4, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_04 (increasingFourValues (N := 53) ⟨⟨4, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a04
    (q : IncreasingFourTail 51 (⟨4, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨4, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_04 _ valid53_04 (cover53_04 q)

end MinModulus.SHCFiveCertificate.Generated
