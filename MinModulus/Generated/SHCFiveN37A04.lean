import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_04 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 402, 642, 2626, 403, 643, 2786, 209, 713, 321, 85, 589, 2631, 20, 524, 2306, 4234, 385, 4265, 2305, 2546, 3746, 3586, 12, 3024, 386]

private theorem valid37_04 : ∀ code ∈ codes37_04, validRelationCode code := by
  decide

private theorem cover37_04 : ∀ q : IncreasingFourTail 35 (⟨4, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_04 (increasingFourValues (N := 37) ⟨⟨4, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a04
    (q : IncreasingFourTail 35 (⟨4, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨4, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_04 _ valid37_04 (cover37_04 q)

end MinModulus.SHCFiveCertificate.Generated
