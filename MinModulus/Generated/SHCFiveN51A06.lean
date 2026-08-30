import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_06 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 402, 642, 2626, 403, 643, 2786, 153, 773, 4387, 4232, 2468, 589, 85, 2631, 4234, 4884, 3765, 1507, 321, 26, 21, 385, 20, 2306, 641, 2546, 524, 3586, 3746, 2064, 2466, 209, 713, 518, 401, 2305, 10, 1905, 4265, 2465, 12, 2944, 2148, 4425, 1837, 3185, 775, 2788, 525, 4547, 2628, 4237, 2624, 155, 774, 387, 527, 3756, 3907, 1827, 278, 11, 1587, 449, 217, 837, 5504, 1187, 770, 25, 4584, 4224, 3587, 1993, 833, 5045, 4066, 28, 154, 526, 14, 465, 89, 769, 13, 3264, 2485, 1546, 4866]

private theorem valid51_06 : ∀ code ∈ codes51_06, validRelationCode code := by
  decide

private theorem cover51_06 : ∀ q : IncreasingFourTail 49 (⟨6, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_06 (increasingFourValues (N := 51) ⟨⟨6, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a06
    (q : IncreasingFourTail 49 (⟨6, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨6, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_06 _ valid51_06 (cover51_06 q)

end MinModulus.SHCFiveCertificate.Generated
