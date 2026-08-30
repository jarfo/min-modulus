import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_28 : List ℕ := [17, 521, 261, 772]

private theorem valid37_28 : ∀ code ∈ codes37_28, validRelationCode code := by
  decide

private theorem cover37_28 : ∀ q : IncreasingFourTail 35 (⟨28, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_28 (increasingFourValues (N := 37) ⟨⟨28, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a28
    (q : IncreasingFourTail 35 (⟨28, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨28, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_28 _ valid37_28 (cover37_28 q)

end MinModulus.SHCFiveCertificate.Generated
