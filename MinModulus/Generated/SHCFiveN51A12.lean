import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_12 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 773, 403, 643, 4387, 2786, 2631, 2468, 4884, 4234, 1507, 518, 4265, 2305, 10, 11, 519, 278, 321, 1905, 713, 2465, 209, 4425, 2624, 1187, 1186, 279, 4584, 2064, 1825, 3904, 337, 201, 2024, 262, 2148, 386, 387, 522, 3586, 18, 523, 385, 89, 2944, 3757, 12, 770, 3912, 193, 1665, 3906, 577, 3907, 1992, 1984, 2954, 1546, 2546, 3746, 833, 3745, 1667, 2648, 449, 4876, 524, 771, 5504, 2545, 4865, 4067, 1528, 3273, 28, 898, 774, 641, 769, 525, 899, 4870, 2067]

private theorem valid51_12 : ∀ code ∈ codes51_12, validRelationCode code := by
  decide

private theorem cover51_12 : ∀ q : IncreasingFourTail 49 (⟨12, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_12 (increasingFourValues (N := 51) ⟨⟨12, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a12
    (q : IncreasingFourTail 49 (⟨12, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨12, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_12 _ valid51_12 (cover51_12 q)

end MinModulus.SHCFiveCertificate.Generated
