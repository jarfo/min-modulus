import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_05 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 3785, 2485, 403, 2786, 643, 642, 402, 2626, 85, 153, 2631, 589, 4232, 4387, 773, 2468, 4234, 3765, 4884, 1347, 2306, 524, 641, 27, 401, 209, 2788, 2633, 774, 4425, 4237, 2628, 4385, 217, 2465, 770, 1988, 775, 21, 20, 385, 154, 525, 3746, 2466, 4547, 321, 89, 10, 3344, 2546, 3586, 12, 2944, 1187, 713, 387, 3907, 386, 4544, 3185, 1905, 897, 3024, 2305, 1993, 449, 465, 1827, 4397, 898, 1546, 3906, 4552, 2478, 26, 30, 769, 13, 771, 31]

private theorem valid51_05 : ∀ code ∈ codes51_05, validRelationCode code := by
  decide

private theorem cover51_05 : ∀ q : IncreasingFourTail 49 (⟨5, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_05 (increasingFourValues (N := 51) ⟨⟨5, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a05
    (q : IncreasingFourTail 49 (⟨5, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨5, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_05 _ valid51_05 (cover51_05 q)

end MinModulus.SHCFiveCertificate.Generated
