import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_07 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 772, 4227, 2308, 201, 337, 577, 153, 773, 402, 4387, 4232, 2468, 642, 2626, 1825, 2786, 643, 522, 1665, 262, 18, 403, 2631, 589, 85, 4234, 4884, 833, 209, 523, 5036, 775, 263, 4425, 12, 14, 1186, 641, 279, 2064, 3765, 386, 10]

private theorem valid37_07 : ∀ code ∈ codes37_07, validRelationCode code := by
  decide

private theorem cover37_07 : ∀ q : IncreasingFourTail 35 (⟨7, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_07 (increasingFourValues (N := 37) ⟨⟨7, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a07
    (q : IncreasingFourTail 35 (⟨7, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨7, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_07 _ valid37_07 (cover37_07 q)

end MinModulus.SHCFiveCertificate.Generated
