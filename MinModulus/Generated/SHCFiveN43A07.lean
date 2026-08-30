import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_07 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 772, 4227, 2308, 19, 523, 263, 153, 773, 4387, 4232, 2468, 209, 713, 321, 3765, 402, 642, 2786, 2626, 1347, 643, 1825, 403, 1665, 589, 85, 2631, 3746, 385, 4234, 2546, 3586, 833, 2624, 12, 14, 2465, 5025, 524, 1993, 2064, 1905, 2148, 641, 27, 4584, 4884, 449, 25, 15, 4864, 386, 770, 2944, 1346, 1827, 30]

private theorem valid43_07 : ∀ code ∈ codes43_07, validRelationCode code := by
  decide

private theorem cover43_07 : ∀ q : IncreasingFourTail 41 (⟨7, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_07 (increasingFourValues (N := 43) ⟨⟨7, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a07
    (q : IncreasingFourTail 41 (⟨7, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨7, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_07 _ valid43_07 (cover43_07 q)

end MinModulus.SHCFiveCertificate.Generated
