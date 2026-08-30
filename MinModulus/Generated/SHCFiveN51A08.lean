import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_08 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 772, 4227, 2308, 1825, 3765, 4387, 4232, 773, 2468, 153, 643, 642, 85, 1665, 2626, 589, 402, 403, 2786, 2631, 1507, 4234, 4884, 321, 2064, 3785, 2624, 209, 3586, 518, 2485, 385, 3746, 2306, 524, 2148, 401, 2546, 713, 2466, 20, 1988, 774, 641, 525, 775, 21, 1868, 770, 5184, 1993, 1187, 12, 387, 4865, 2465, 10, 89, 3185, 386, 4385, 2305, 154, 771, 1905, 1587, 1828, 837, 4087, 217, 4584, 4265, 1186, 4237, 5514, 4707, 2788, 28, 25, 5204, 4224, 5025, 4066, 3946, 4547, 3587, 24, 449, 2067]

private theorem valid51_08 : ∀ code ∈ codes51_08, validRelationCode code := by
  decide

private theorem cover51_08 : ∀ q : IncreasingFourTail 49 (⟨8, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_08 (increasingFourValues (N := 51) ⟨⟨8, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a08
    (q : IncreasingFourTail 49 (⟨8, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨8, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_08 _ valid51_08 (cover51_08 q)

end MinModulus.SHCFiveCertificate.Generated
