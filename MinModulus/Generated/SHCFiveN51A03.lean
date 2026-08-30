import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_03 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 524, 2306, 20, 643, 403, 2786, 642, 402, 2626, 85, 589, 2631, 21, 775, 2788, 155, 4707, 4385, 774, 4225, 4544, 705, 641, 23, 4230, 2628, 4224, 2648, 2546, 4234, 2466, 4547, 4237, 2476, 465, 401, 1186, 3185, 773, 525, 2468, 3025, 2478, 526, 387, 3746, 3344, 2148, 3586, 386, 1988, 385, 3786, 3756, 3906, 1346, 5665, 770, 2866, 837, 4066, 3118, 1668, 1993, 5514, 5510, 4870, 5191, 4387, 2948, 899, 898, 217, 897, 153, 5504, 4866, 4871]

private theorem valid51_03 : ∀ code ∈ codes51_03, validRelationCode code := by
  decide

private theorem cover51_03 : ∀ q : IncreasingFourTail 49 (⟨3, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_03 (increasingFourValues (N := 51) ⟨⟨3, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a03
    (q : IncreasingFourTail 49 (⟨3, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨3, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_03 _ valid51_03 (cover51_03 q)

end MinModulus.SHCFiveCertificate.Generated
