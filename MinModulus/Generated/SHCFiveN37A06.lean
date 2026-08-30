import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_06 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 2308, 1507, 321, 2626, 772, 4227, 262, 209, 713, 263, 19, 523, 402, 642, 1825, 2465, 1665, 1905, 4425, 3765, 773, 4387, 2468, 643, 26, 4232, 449, 403, 2064, 2786, 2631, 4584, 3586, 1828, 518, 2624, 1827, 774, 153, 20, 278]

private theorem valid37_06 : ∀ code ∈ codes37_06, validRelationCode code := by
  decide

private theorem cover37_06 : ∀ q : IncreasingFourTail 35 (⟨6, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_06 (increasingFourValues (N := 37) ⟨⟨6, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a06
    (q : IncreasingFourTail 35 (⟨6, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨6, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_06 _ valid37_06 (cover37_06 q)

end MinModulus.SHCFiveCertificate.Generated
