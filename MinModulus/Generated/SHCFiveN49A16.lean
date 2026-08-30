import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_16 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 4584, 4425, 4265, 278, 279, 589, 403, 153, 773, 4884, 4227, 2308, 2626, 642, 4387, 85, 2631, 2305, 1507, 643, 4232, 2624, 10, 11, 321, 2786, 2468, 1905, 2465, 209, 518, 2064, 519, 1825, 1546, 4234, 193, 1506, 5025, 1665, 1527, 262, 6, 201, 385, 3273, 1187, 1837, 2067, 12, 386, 2024, 5184, 18, 522, 449, 217, 23, 31]

private theorem valid49_16 : ∀ code ∈ codes49_16, validRelationCode code := by
  decide

private theorem cover49_16 : ∀ q : IncreasingFourTail 47 (⟨16, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_16 (increasingFourValues (N := 49) ⟨⟨16, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a16
    (q : IncreasingFourTail 47 (⟨16, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨16, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_16 _ valid49_16 (cover49_16 q)

end MinModulus.SHCFiveCertificate.Generated
