import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_03 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 524, 2306, 20, 643, 403, 2786, 402, 2626, 642, 775, 3765, 2788, 4707, 1988, 770, 4385, 5025, 3907, 385, 774, 589, 401, 5045, 4870, 154, 89, 3185, 525, 1347, 12, 2546, 2067, 3912, 526, 465, 769, 5665]

private theorem valid39_03 : ∀ code ∈ codes39_03, validRelationCode code := by
  decide

private theorem cover39_03 : ∀ q : IncreasingFourTail 37 (⟨3, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_03 (increasingFourValues (N := 39) ⟨⟨3, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a03
    (q : IncreasingFourTail 37 (⟨3, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨3, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_03 _ valid39_03 (cover39_03 q)

end MinModulus.SHCFiveCertificate.Generated
