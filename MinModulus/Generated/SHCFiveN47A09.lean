import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_09 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 4227, 577, 772, 2308, 18, 522, 262, 153, 773, 4387, 4232, 2468, 402, 642, 2626, 1825, 2786, 1665, 643, 403, 2631, 589, 85, 4234, 523, 263, 4884, 19, 209, 713, 321, 4425, 1186, 2624, 4584, 1905, 4265, 2465, 2064, 1347, 518, 385, 2305, 10, 3757, 524, 770, 833, 4237, 12, 2628, 401, 641, 154, 26, 2306, 387, 4385, 3765, 774, 278, 217, 837, 898, 769, 3264, 4225, 2466, 5036, 386, 89, 519, 5025]

private theorem valid47_09 : ∀ code ∈ codes47_09, validRelationCode code := by
  decide

private theorem cover47_09 : ∀ q : IncreasingFourTail 45 (⟨9, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_09 (increasingFourValues (N := 47) ⟨⟨9, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a09
    (q : IncreasingFourTail 45 (⟨9, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨9, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_09 _ valid47_09 (cover47_09 q)

end MinModulus.SHCFiveCertificate.Generated
