import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_12 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 4584, 4425, 4265, 278, 2546, 153, 773, 403, 4884, 279, 589, 2626, 4227, 4232, 2308, 10, 85, 193, 385, 1868, 2465, 2631, 518, 2305, 642, 6, 11, 519, 4387, 22, 526, 321]

private theorem valid37_12 : ∀ code ∈ codes37_12, validRelationCode code := by
  decide

private theorem cover37_12 : ∀ q : IncreasingFourTail 35 (⟨12, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_12 (increasingFourValues (N := 37) ⟨⟨12, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a12
    (q : IncreasingFourTail 35 (⟨12, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨12, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_12 _ valid37_12 (cover37_12 q)

end MinModulus.SHCFiveCertificate.Generated
