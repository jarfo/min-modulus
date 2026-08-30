import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_07 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 3765, 642, 4387, 4232, 402, 2626, 403, 2786, 589, 2631, 643, 773, 2468, 85, 153, 4234, 4884, 209, 321, 2465, 4425, 713, 1905, 2624, 833, 385, 21, 2546, 10, 3746, 2064, 4870, 2148, 524, 525, 641, 518, 2306, 4584, 2305, 12, 4265, 14, 11, 3757, 278, 401, 3264, 449, 3756, 4552, 519, 4397, 3273, 3344, 4544, 5036, 1187, 20, 2944, 1347, 3587, 4237, 3907, 24, 154, 2954, 4866, 1907, 4547, 898, 22, 526, 30, 217, 899, 387, 5504]

private theorem valid49_07 : ∀ code ∈ codes49_07, validRelationCode code := by
  decide

private theorem cover49_07 : ∀ q : IncreasingFourTail 47 (⟨7, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_07 (increasingFourValues (N := 49) ⟨⟨7, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a07
    (q : IncreasingFourTail 47 (⟨7, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨7, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_07 _ valid49_07 (cover49_07 q)

end MinModulus.SHCFiveCertificate.Generated
