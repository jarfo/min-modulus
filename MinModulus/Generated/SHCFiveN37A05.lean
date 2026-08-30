import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_05 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 2308, 263, 772, 4227, 1825, 3765, 1665, 642, 643, 402, 403, 2786, 2626, 589, 2631, 85, 2064, 209, 4584, 2624, 713, 321, 1905, 518, 4425, 2465, 10, 278, 1528, 4265, 2305, 4234, 21, 4224, 1988]

private theorem valid37_05 : ∀ code ∈ codes37_05, validRelationCode code := by
  decide

private theorem cover37_05 : ∀ q : IncreasingFourTail 35 (⟨5, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_05 (increasingFourValues (N := 37) ⟨⟨5, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a05
    (q : IncreasingFourTail 35 (⟨5, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨5, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_05 _ valid37_05 (cover37_05 q)

end MinModulus.SHCFiveCertificate.Generated
