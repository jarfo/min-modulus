import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_10 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 772, 4227, 2308, 18, 522, 262, 153, 773, 4387, 4232, 2468, 523, 263, 19, 4884, 402, 1825, 2626, 643, 642, 1665, 2786, 403, 2631, 589, 85, 4234, 2064, 321, 1507, 713, 209, 2624, 1905, 518, 4425, 2465, 4584, 4265, 2305, 1186, 10, 385, 2546, 3746, 278, 2306, 525, 3185, 20, 524, 4547, 12, 2944, 3586, 13, 387, 386, 21, 775, 3906, 2954, 401, 4385, 2466, 774, 3264, 641, 4225, 2866, 770, 837, 4224, 519, 2706, 3767, 1828, 833, 897, 771, 5514, 3765, 449, 217, 2945, 1868, 2648, 193, 77, 25, 899, 5204, 4874, 3105]

private theorem valid53_10 : ∀ code ∈ codes53_10, validRelationCode code := by
  decide

private theorem cover53_10 : ∀ q : IncreasingFourTail 51 (⟨10, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_10 (increasingFourValues (N := 53) ⟨⟨10, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a10
    (q : IncreasingFourTail 51 (⟨10, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨10, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_10 _ valid53_10 (cover53_10 q)

end MinModulus.SHCFiveCertificate.Generated
