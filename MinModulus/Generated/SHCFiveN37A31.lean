import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_31 : List ℕ := [772]

private theorem valid37_31 : ∀ code ∈ codes37_31, validRelationCode code := by
  decide

private theorem cover37_31 : ∀ q : IncreasingFourTail 35 (⟨31, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_31 (increasingFourValues (N := 37) ⟨⟨31, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a31
    (q : IncreasingFourTail 35 (⟨31, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨31, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_31 _ valid37_31 (cover37_31 q)

end MinModulus.SHCFiveCertificate.Generated
