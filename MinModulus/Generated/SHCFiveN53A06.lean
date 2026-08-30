import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_06 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 402, 642, 2626, 403, 643, 2786, 153, 773, 4387, 4232, 2468, 589, 85, 2631, 4234, 4884, 3765, 1507, 321, 21, 4385, 20, 641, 26, 2306, 524, 154, 774, 2628, 837, 217, 525, 155, 775, 713, 3185, 401, 12, 2305, 1187, 4547, 2064, 4225, 1837, 10, 2546, 385, 3746, 209, 2788, 2465, 518, 4224, 2466, 3586, 1667, 2148, 4425, 1905, 1993, 770, 2624, 2633, 4584, 4397, 4544, 1907, 2478, 4265, 1186, 465, 89, 3747, 11, 3785, 24, 278, 23, 3264, 14, 30, 93, 897, 25, 29, 527, 2147, 3912, 526, 961, 769, 387, 3344, 5204, 3946, 4866]

private theorem valid53_06 : ∀ code ∈ codes53_06, validRelationCode code := by
  decide

private theorem cover53_06 : ∀ q : IncreasingFourTail 51 (⟨6, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_06 (increasingFourValues (N := 53) ⟨⟨6, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a06
    (q : IncreasingFourTail 51 (⟨6, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨6, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_06 _ valid53_06 (cover53_06 q)

end MinModulus.SHCFiveCertificate.Generated
