import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_07 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 3765, 642, 4387, 4232, 402, 153, 773, 2786, 2626, 2631, 643, 85, 403, 589, 2468, 4234, 4884, 209, 321, 2465, 4425, 713, 1905, 2624, 833, 2305, 10, 13, 3264, 1347, 154, 385, 1187, 12, 449, 20, 14, 11, 524, 3756, 155, 27, 837, 4397, 641, 401, 4584, 2064, 3586, 2028, 21, 5025, 774, 1993, 770, 4237, 2788, 2628, 1668, 4870, 518, 525, 4865, 2148, 898, 705, 897, 3746, 1528, 386, 899, 519, 4224, 93, 769, 29, 5504, 1586, 1827, 1837, 2478, 24, 26, 278, 217, 387, 775, 279, 4544, 5514, 2466]

private theorem valid51_07 : ∀ code ∈ codes51_07, validRelationCode code := by
  decide

private theorem cover51_07 : ∀ q : IncreasingFourTail 49 (⟨7, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_07 (increasingFourValues (N := 51) ⟨⟨7, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a07
    (q : IncreasingFourTail 49 (⟨7, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨7, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_07 _ valid51_07 (cover51_07 q)

end MinModulus.SHCFiveCertificate.Generated
