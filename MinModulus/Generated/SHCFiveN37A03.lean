import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_03 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 3785, 4227, 2308, 2485, 524, 2306, 20, 402, 642, 2626, 403, 643, 2786, 385, 2546, 3185, 3746, 4385, 3765, 21, 525, 3344, 154, 774, 465, 401, 4707, 589, 775, 12, 770, 85, 153]

private theorem valid37_03 : ∀ code ∈ codes37_03, validRelationCode code := by
  decide

private theorem cover37_03 : ∀ q : IncreasingFourTail 35 (⟨3, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_03 (increasingFourValues (N := 37) ⟨⟨3, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a03
    (q : IncreasingFourTail 35 (⟨3, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨3, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_03 _ valid37_03 (cover37_03 q)

end MinModulus.SHCFiveCertificate.Generated
