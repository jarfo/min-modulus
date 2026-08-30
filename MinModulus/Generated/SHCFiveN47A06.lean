import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_06 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 402, 642, 2626, 403, 643, 2786, 153, 773, 4387, 4232, 2468, 589, 85, 2631, 3765, 4234, 321, 4884, 2305, 26, 2064, 4265, 1905, 209, 713, 518, 2465, 10, 4425, 5025, 1507, 2485, 2466, 2148, 775, 401, 155, 774, 3586, 524, 15, 2628, 2624, 2306, 385, 641, 217, 2788, 4584, 20, 12, 837, 11, 4397, 2808, 14, 525, 1508, 1993, 1586, 3786, 3946, 2227, 4547, 22, 77, 5184]

private theorem valid47_06 : ∀ code ∈ codes47_06, validRelationCode code := by
  decide

private theorem cover47_06 : ∀ q : IncreasingFourTail 45 (⟨6, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_06 (increasingFourValues (N := 47) ⟨⟨6, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a06
    (q : IncreasingFourTail 45 (⟨6, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨6, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_06 _ valid47_06 (cover47_06 q)

end MinModulus.SHCFiveCertificate.Generated
