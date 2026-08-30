import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_08 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 772, 4227, 2308, 18, 522, 262, 153, 773, 4387, 4232, 2468, 523, 263, 19, 4884, 321, 2064, 2624, 209, 713, 518, 10, 4584, 3765, 642, 643, 2626, 85, 402, 589, 1665, 403, 2465, 1825, 1905, 1507, 2786, 4234, 385, 5184, 2631, 3746, 524, 2305, 1186, 20, 2546, 2306, 387, 4425, 1586, 1868, 641, 3264, 4265, 4106, 1988, 833, 2944, 278, 217, 401, 3105, 5025, 769, 13, 771]

private theorem valid45_08 : ∀ code ∈ codes45_08, validRelationCode code := by
  decide

private theorem cover45_08 : ∀ q : IncreasingFourTail 43 (⟨8, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_08 (increasingFourValues (N := 45) ⟨⟨8, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a08
    (q : IncreasingFourTail 43 (⟨8, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨8, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_08 _ valid45_08 (cover45_08 q)

end MinModulus.SHCFiveCertificate.Generated
