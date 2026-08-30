import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_10 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 4227, 642, 772, 2308, 577, 402, 2626, 1825, 18, 522, 262, 1665, 403, 643, 2786, 153, 773, 4387, 4232, 2468, 589, 85, 2631, 4234, 523, 263, 4884, 19, 2064, 209, 321, 713, 4265, 1186, 518, 2624, 1905, 4425, 4584, 2546, 2305, 385, 2465, 10, 1507, 278, 3746, 2306, 524, 387, 2866, 20, 2466, 3906, 217, 641, 4066, 770, 401, 3927, 386, 2944, 3586, 4230, 4106, 3786, 12, 3911, 2808, 1828, 837, 775, 4865, 449, 705, 897, 5504, 26, 193, 833, 21, 771, 519, 15, 31]

private theorem valid51_10 : ∀ code ∈ codes51_10, validRelationCode code := by
  decide

private theorem cover51_10 : ∀ q : IncreasingFourTail 49 (⟨10, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_10 (increasingFourValues (N := 51) ⟨⟨10, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a10
    (q : IncreasingFourTail 49 (⟨10, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨10, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_10 _ valid51_10 (cover51_10 q)

end MinModulus.SHCFiveCertificate.Generated
