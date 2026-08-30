import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_04 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 642, 402, 2626, 524, 2306, 403, 2786, 643, 1507, 20, 85, 589, 2631, 773, 2468, 4387, 153, 4232, 3765, 21, 641, 2466, 401, 385, 525, 4234, 775, 2788, 774, 4547, 2546, 4237, 2628, 4224, 4225, 1993, 2633, 449, 321, 217, 3746, 705, 387, 155, 4385, 22, 2305, 3024, 3185, 1988, 23, 3907, 770, 4265, 5510, 465, 2866, 1186, 2648, 526, 3786, 3946, 386, 2476, 3911, 2148, 154, 14, 5504, 5346, 3586, 4397, 2808, 833, 771, 4544, 4884]

private theorem valid51_04 : ∀ code ∈ codes51_04, validRelationCode code := by
  decide

private theorem cover51_04 : ∀ q : IncreasingFourTail 49 (⟨4, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_04 (increasingFourValues (N := 51) ⟨⟨4, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a04
    (q : IncreasingFourTail 49 (⟨4, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨4, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_04 _ valid51_04 (cover51_04 q)

end MinModulus.SHCFiveCertificate.Generated
