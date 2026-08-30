import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_05 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 3785, 2485, 642, 402, 2626, 403, 643, 2786, 85, 589, 2631, 153, 773, 2468, 4232, 4387, 4234, 3765, 21, 2306, 641, 4385, 20, 524, 401, 2466, 3185, 525, 2546, 27, 385, 3746, 4224, 14, 774, 4425, 209, 2465, 713, 2628, 4225, 775, 217, 89, 3024, 2633, 387, 1528, 3906, 2808, 4544, 4547, 4237, 4230, 154, 1905, 2478, 2706, 5204, 10, 155, 321, 3025, 2305, 386, 4265, 3907, 23, 2958, 2944, 5186, 24, 12, 22, 705, 837, 5665, 3586, 1827, 770, 771, 2954, 4870, 5191, 2648, 465, 899, 3264, 5504, 4864, 2950, 3747]

private theorem valid53_05 : ∀ code ∈ codes53_05, validRelationCode code := by
  decide

private theorem cover53_05 : ∀ q : IncreasingFourTail 51 (⟨5, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_05 (increasingFourValues (N := 53) ⟨⟨5, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a05
    (q : IncreasingFourTail 51 (⟨5, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨5, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_05 _ valid53_05 (cover53_05 q)

end MinModulus.SHCFiveCertificate.Generated
