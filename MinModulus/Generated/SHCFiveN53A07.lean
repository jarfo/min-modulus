import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_07 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 3765, 642, 4387, 4232, 402, 773, 153, 2626, 2786, 2631, 643, 85, 403, 589, 2468, 4234, 4884, 209, 321, 2465, 4425, 713, 1905, 2624, 1528, 2305, 1187, 1347, 10, 833, 14, 1837, 2148, 385, 1868, 20, 641, 154, 3264, 524, 12, 11, 770, 837, 401, 155, 3746, 2944, 2306, 3586, 3757, 2628, 4870, 4237, 2788, 2064, 21, 4224, 5025, 4397, 386, 775, 449, 525, 3785, 2546, 25, 5204, 3344, 4230, 2466, 774, 3024, 5514, 1548, 898, 526, 29, 15, 5184, 5346, 3747, 3273, 518, 93, 4584, 961, 217, 77, 769, 387, 771, 23, 2954, 4225, 4865]

private theorem valid53_07 : ∀ code ∈ codes53_07, validRelationCode code := by
  decide

private theorem cover53_07 : ∀ q : IncreasingFourTail 51 (⟨7, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_07 (increasingFourValues (N := 53) ⟨⟨7, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a07
    (q : IncreasingFourTail 51 (⟨7, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨7, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_07 _ valid53_07 (cover53_07 q)

end MinModulus.SHCFiveCertificate.Generated
