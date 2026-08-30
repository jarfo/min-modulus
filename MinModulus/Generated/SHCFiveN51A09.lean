import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_09 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 2308, 1347, 1825, 2468, 2626, 2786, 1665, 262, 772, 4227, 402, 642, 643, 4232, 403, 153, 523, 19, 263, 773, 4387, 2631, 589, 85, 4884, 4234, 3765, 209, 321, 713, 2465, 385, 2624, 4425, 1905, 3757, 2064, 3586, 10, 12, 3746, 1837, 641, 1186, 524, 2944, 2546, 3264, 1187, 449, 2148, 518, 401, 1993, 387, 3946, 386, 3906, 4584, 3927, 525, 833, 4066, 837, 2866, 2306, 4237, 3273, 899, 775, 4707, 4087, 771, 4265, 3907, 20, 28, 898, 21, 770, 774, 155, 4224, 4870, 3756, 1827]

private theorem valid51_09 : ∀ code ∈ codes51_09, validRelationCode code := by
  decide

private theorem cover51_09 : ∀ q : IncreasingFourTail 49 (⟨9, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_09 (increasingFourValues (N := 51) ⟨⟨9, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a09
    (q : IncreasingFourTail 49 (⟨9, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨9, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_09 _ valid51_09 (cover51_09 q)

end MinModulus.SHCFiveCertificate.Generated
