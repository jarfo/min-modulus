import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_12 : List ℕ := [17, 521, 261, 131, 772, 402, 279, 589, 403, 713, 4265, 278, 4584, 4425, 153, 773, 4884, 1507, 2308, 2626, 642, 4227, 2631, 4387, 643, 321, 2786, 2305, 2468, 1905, 10, 4232, 518, 2465, 85, 209, 2624, 11, 519, 4234, 2064, 770, 1186, 3586, 1993, 2958, 3912, 387, 5191, 385, 641, 12, 89, 5186, 18, 193, 13, 775, 3757, 3907, 4066, 1546, 386, 2954, 2546, 4067, 3118, 20, 525, 1825, 2067, 2648, 25, 1984, 262, 6, 217, 769, 5025, 5505, 524, 774, 22, 30, 201, 337, 837, 401, 29, 899, 155]

private theorem valid49_12 : ∀ code ∈ codes49_12, validRelationCode code := by
  decide

private theorem cover49_12 : ∀ q : IncreasingFourTail 47 (⟨12, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_12 (increasingFourValues (N := 49) ⟨⟨12, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a12
    (q : IncreasingFourTail 47 (⟨12, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨12, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_12 _ valid49_12 (cover49_12 q)

end MinModulus.SHCFiveCertificate.Generated
