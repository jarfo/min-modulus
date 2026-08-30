import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_08 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 772, 4227, 2308, 1825, 19, 523, 263, 3765, 1507, 4232, 2468, 4387, 773, 153, 403, 643, 402, 2786, 1665, 642, 2626, 85, 2631, 589, 4234, 4884, 321, 2064, 3586, 3746, 12, 385, 2546, 2624, 1837, 5184, 20, 524, 1187, 2944, 4237, 209, 2306, 2148, 525, 387, 4066, 713, 401, 1186, 641, 4547, 518, 449, 2866, 1993, 14, 10, 155, 775, 154, 833, 837, 899, 2466, 4584, 2305, 1827, 1905, 278, 769, 27, 4224, 3906, 1548, 26, 25, 771, 3264]

private theorem valid49_08 : ∀ code ∈ codes49_08, validRelationCode code := by
  decide

private theorem cover49_08 : ∀ q : IncreasingFourTail 47 (⟨8, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_08 (increasingFourValues (N := 49) ⟨⟨8, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a08
    (q : IncreasingFourTail 47 (⟨8, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨8, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_08 _ valid49_08 (cover49_08 q)

end MinModulus.SHCFiveCertificate.Generated
