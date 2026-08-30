import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_09 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 772, 4227, 2308, 19, 523, 263, 153, 773, 4387, 4232, 2468, 4884, 3765, 642, 402, 1825, 2626, 1347, 2786, 1665, 643, 403, 589, 2631, 85, 4234, 3746, 209, 3586, 385, 2546, 321, 12, 713, 2624, 2465, 1905, 4425, 2064, 3757, 10, 1837, 524, 1993, 1187, 14, 21, 1346, 20, 154, 641, 1186, 4584, 401, 525, 518, 833, 2944, 386, 774, 2306, 449, 4237, 4265, 3906, 3946, 3767, 387, 3927, 4066, 2466, 2866, 1546, 278, 897, 5514, 2706, 155, 5184, 4224, 3185, 1667, 770, 837, 775, 1907, 526, 89, 77, 899, 5204, 2950]

private theorem valid53_09 : ∀ code ∈ codes53_09, validRelationCode code := by
  decide

private theorem cover53_09 : ∀ q : IncreasingFourTail 51 (⟨9, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_09 (increasingFourValues (N := 53) ⟨⟨9, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a09
    (q : IncreasingFourTail 51 (⟨9, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨9, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_09 _ valid53_09 (cover53_09 q)

end MinModulus.SHCFiveCertificate.Generated
