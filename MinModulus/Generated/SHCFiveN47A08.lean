import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_08 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 2308, 1507, 262, 772, 4227, 2468, 523, 263, 19, 4232, 153, 773, 4387, 321, 4884, 2626, 402, 643, 3765, 642, 1825, 403, 2786, 1665, 2631, 589, 85, 4234, 385, 3746, 2064, 2546, 3586, 5184, 1837, 2624, 2944, 12, 1187, 449, 21, 2148, 4870, 1988, 154, 525, 524, 518, 209, 770, 833, 10, 401, 27, 15, 713, 837, 4265, 641, 775, 3264, 1993, 26, 771, 20, 898, 89, 897, 899, 4224, 13, 29, 387]

private theorem valid47_08 : ∀ code ∈ codes47_08, validRelationCode code := by
  decide

private theorem cover47_08 : ∀ q : IncreasingFourTail 45 (⟨8, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_08 (increasingFourValues (N := 47) ⟨⟨8, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a08
    (q : IncreasingFourTail 45 (⟨8, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨8, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_08 _ valid47_08 (cover47_08 q)

end MinModulus.SHCFiveCertificate.Generated
