import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_10 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 278, 279, 4425, 4584, 153, 773, 589, 403, 4884, 642, 2626, 4227, 2308, 85, 2631, 4387, 643, 4232, 2468, 10, 2786, 518, 11, 519, 321, 4234, 19, 5025, 1905, 18, 6, 217, 1827, 770, 263]

private theorem valid37_10 : ∀ code ∈ codes37_10, validRelationCode code := by
  decide

private theorem cover37_10 : ∀ q : IncreasingFourTail 35 (⟨10, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_10 (increasingFourValues (N := 37) ⟨⟨10, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a10
    (q : IncreasingFourTail 35 (⟨10, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨10, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_10 _ valid37_10 (cover37_10 q)

end MinModulus.SHCFiveCertificate.Generated
