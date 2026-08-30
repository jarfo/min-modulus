import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_25 : List ℕ := [17, 521, 261, 131, 772, 642, 2626]

private theorem valid37_25 : ∀ code ∈ codes37_25, validRelationCode code := by
  decide

private theorem cover37_25 : ∀ q : IncreasingFourTail 35 (⟨25, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_25 (increasingFourValues (N := 37) ⟨⟨25, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a25
    (q : IncreasingFourTail 35 (⟨25, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨25, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_25 _ valid37_25 (cover37_25 q)

end MinModulus.SHCFiveCertificate.Generated
