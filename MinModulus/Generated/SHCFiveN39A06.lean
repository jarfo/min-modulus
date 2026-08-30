import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_06 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 772, 4227, 2308, 19, 523, 263, 209, 713, 321, 3765, 1507, 1825, 642, 2626, 643, 1665, 2786, 403, 402, 4387, 1905, 26, 2465, 3586, 4232, 524, 2064, 2468, 12, 4584, 153, 773, 4425, 1827, 155, 15, 2624, 3785, 10, 518, 775, 4106, 20, 14, 24, 217, 837, 771]

private theorem valid39_06 : ∀ code ∈ codes39_06, validRelationCode code := by
  decide

private theorem cover39_06 : ∀ q : IncreasingFourTail 37 (⟨6, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_06 (increasingFourValues (N := 39) ⟨⟨6, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a06
    (q : IncreasingFourTail 37 (⟨6, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨6, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_06 _ valid39_06 (cover39_06 q)

end MinModulus.SHCFiveCertificate.Generated
