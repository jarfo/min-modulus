import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_10 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 772, 4227, 2308, 402, 642, 2626, 201, 337, 577, 1825, 403, 643, 2786, 153, 773, 4387, 4232, 2468, 589, 85, 2631, 4234, 522, 1665, 262, 4884, 18, 4265, 523, 263, 209, 713, 1186, 518, 321, 1905, 4425, 2305, 19, 10, 2624, 2465, 4584, 278, 2064, 385, 2546, 3586, 4707, 519, 387, 2866, 3906, 524, 770, 12, 3025, 4865, 20, 386, 4225, 4066, 3746, 3927, 2808, 3907, 1828, 449, 5026, 2188, 154, 774, 14, 961, 193, 899, 5036]

private theorem valid49_10 : ∀ code ∈ codes49_10, validRelationCode code := by
  decide

private theorem cover49_10 : ∀ q : IncreasingFourTail 47 (⟨10, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_10 (increasingFourValues (N := 49) ⟨⟨10, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a10
    (q : IncreasingFourTail 47 (⟨10, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨10, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_10 _ valid49_10 (cover49_10 q)

end MinModulus.SHCFiveCertificate.Generated
