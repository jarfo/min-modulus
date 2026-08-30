import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_08 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 4227, 577, 772, 2308, 402, 642, 2626, 1825, 18, 522, 262, 1665, 403, 643, 2786, 153, 773, 4387, 4232, 2468, 589, 523, 85, 2631, 263, 19, 4234, 4884, 2064, 5184, 321, 209, 385, 2624, 1186, 713, 2546, 518, 3746, 20, 524, 2306, 4584, 1905, 4425, 3906, 154, 10, 21, 27, 2465, 26, 278, 12, 386, 774, 961, 77, 29]

private theorem valid43_08 : ∀ code ∈ codes43_08, validRelationCode code := by
  decide

private theorem cover43_08 : ∀ q : IncreasingFourTail 41 (⟨8, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_08 (increasingFourValues (N := 43) ⟨⟨8, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a08
    (q : IncreasingFourTail 41 (⟨8, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨8, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_08 _ valid43_08 (cover43_08 q)

end MinModulus.SHCFiveCertificate.Generated
