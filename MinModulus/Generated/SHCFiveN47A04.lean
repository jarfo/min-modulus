import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_04 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 642, 402, 2626, 643, 403, 2786, 524, 2306, 20, 85, 589, 2631, 3765, 773, 2468, 209, 153, 401, 2466, 641, 4234, 525, 775, 4237, 4547, 2788, 3185, 2628, 217, 837, 4225, 4224, 774, 321, 770, 2478, 2546, 21, 155, 5045, 2305, 154, 1667, 3586, 4265, 3912, 2633, 465, 385, 387, 3344, 3025, 4230, 22, 4544, 2944, 5510, 3786, 4232, 449, 705, 833, 4865, 2950]

private theorem valid47_04 : ∀ code ∈ codes47_04, validRelationCode code := by
  decide

private theorem cover47_04 : ∀ q : IncreasingFourTail 45 (⟨4, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_04 (increasingFourValues (N := 47) ⟨⟨4, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a04
    (q : IncreasingFourTail 45 (⟨4, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨4, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_04 _ valid47_04 (cover47_04 q)

end MinModulus.SHCFiveCertificate.Generated
