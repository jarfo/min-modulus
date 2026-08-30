import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_30 : List ℕ := [17, 402]

private theorem valid37_30 : ∀ code ∈ codes37_30, validRelationCode code := by
  decide

private theorem cover37_30 : ∀ q : IncreasingFourTail 35 (⟨30, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_30 (increasingFourValues (N := 37) ⟨⟨30, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a30
    (q : IncreasingFourTail 35 (⟨30, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨30, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_30 _ valid37_30 (cover37_30 q)

end MinModulus.SHCFiveCertificate.Generated
