import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_17 : List ℕ := [1185]

private theorem valid37_17 : ∀ code ∈ codes37_17, validRelationCode code := by
  decide

private theorem cover37_17 : ∀ q : IncreasingFourTail 35 (⟨17, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_17 (increasingFourValues (N := 37) ⟨⟨17, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a17
    (q : IncreasingFourTail 35 (⟨17, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨17, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_17 _ valid37_17 (cover37_17 q)

end MinModulus.SHCFiveCertificate.Generated
