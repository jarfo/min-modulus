import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_06 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 772, 4227, 2308, 1665, 402, 642, 2626, 3765, 209, 643, 85, 713, 321, 589, 403, 2786, 2631, 4234, 773, 2468, 153, 4232, 4387, 26, 2064, 4884, 2305, 1905, 4265, 2148, 518, 2465, 10, 4425, 21, 1993, 775, 4584, 2624, 2306, 524, 278, 2788, 705, 217, 525, 4544, 2485, 4397, 4552, 25, 155, 1668, 774, 385, 387, 3264]

private theorem valid43_06 : ∀ code ∈ codes43_06, validRelationCode code := by
  decide

private theorem cover43_06 : ∀ q : IncreasingFourTail 41 (⟨6, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_06 (increasingFourValues (N := 43) ⟨⟨6, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a06
    (q : IncreasingFourTail 41 (⟨6, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨6, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_06 _ valid43_06 (cover43_06 q)

end MinModulus.SHCFiveCertificate.Generated
