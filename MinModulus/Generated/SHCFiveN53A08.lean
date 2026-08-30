import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_08 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 772, 4227, 2308, 1665, 402, 642, 2626, 3765, 4387, 4232, 643, 85, 773, 2468, 589, 2631, 153, 403, 2786, 4234, 4884, 1507, 321, 2064, 2148, 209, 2624, 1905, 2305, 518, 713, 2465, 4265, 4425, 10, 4584, 2306, 524, 775, 3586, 2485, 3785, 5184, 1868, 21, 1528, 20, 401, 3756, 2466, 4547, 4237, 774, 89, 3185, 385, 387, 4870, 155, 1827, 154, 770, 3025, 4865, 525, 1837, 2628, 5025, 4225, 3746, 1587, 1988, 2546, 3911, 837, 4224, 3912, 24, 25, 26, 449, 641, 771, 3946, 1187, 12, 28, 898, 386, 465, 705, 217, 833, 93, 897, 29, 27]

private theorem valid53_08 : ∀ code ∈ codes53_08, validRelationCode code := by
  decide

private theorem cover53_08 : ∀ q : IncreasingFourTail 51 (⟨8, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_08 (increasingFourValues (N := 53) ⟨⟨8, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a08
    (q : IncreasingFourTail 51 (⟨8, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨8, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_08 _ valid53_08 (cover53_08 q)

end MinModulus.SHCFiveCertificate.Generated
