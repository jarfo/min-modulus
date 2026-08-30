import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_09 : List ℕ := [17, 521, 261, 131, 2024, 402, 3904, 772, 589, 403, 642, 2626, 4227, 2308, 643, 2786, 4232, 2468, 85, 153, 773, 2631, 4234, 4387, 4884, 201, 337, 2704, 1825, 577, 209, 262, 4425, 522, 1665, 713, 321, 1905, 4265, 18, 2465, 3765, 10, 2305, 518, 2624, 278, 4584, 263, 523, 2064, 775, 12, 837, 519, 20, 770, 217, 385, 5025, 386, 641, 387]

private theorem valid43_09 : ∀ code ∈ codes43_09, validRelationCode code := by
  decide

private theorem cover43_09 : ∀ q : IncreasingFourTail 41 (⟨9, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_09 (increasingFourValues (N := 43) ⟨⟨9, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a09
    (q : IncreasingFourTail 41 (⟨9, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨9, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_09 _ valid43_09 (cover43_09 q)

end MinModulus.SHCFiveCertificate.Generated
