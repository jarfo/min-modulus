import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_13 : List ℕ := [17, 521, 261, 131, 772, 278, 4265, 402, 4584, 279, 713, 4425, 589, 403, 153, 773, 4884, 642, 2626, 1186, 85, 2631, 643, 4227, 2308, 2786, 2468, 4232, 209, 4234, 4387, 2624, 321, 2465, 1905, 2064, 518, 2305, 10, 11, 519, 1187, 1347, 1528, 833, 770, 193, 1865, 3585, 3907, 3757, 18, 522, 1546, 2148, 1984, 3745, 577, 263, 1988, 6, 387, 30, 337, 897, 5510, 1868, 837, 3767, 3273, 24, 386, 262, 641, 5504, 2944, 2866, 3746, 12, 898, 705, 217, 525, 5191]

private theorem valid49_13 : ∀ code ∈ codes49_13, validRelationCode code := by
  decide

private theorem cover49_13 : ∀ q : IncreasingFourTail 47 (⟨13, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_13 (increasingFourValues (N := 49) ⟨⟨13, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a13
    (q : IncreasingFourTail 47 (⟨13, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨13, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_13 _ valid49_13 (cover49_13 q)

end MinModulus.SHCFiveCertificate.Generated
