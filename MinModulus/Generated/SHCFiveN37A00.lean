import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_00 : List ℕ := [1344]

private theorem valid37_00 : ∀ code ∈ codes37_00, validRelationCode code := by
  decide

private theorem cover37_00 : ∀ q : IncreasingFourTail 35 (⟨0, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_00 (increasingFourValues (N := 37) ⟨⟨0, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a00
    (q : IncreasingFourTail 35 (⟨0, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨0, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_00 _ valid37_00 (cover37_00 q)

end MinModulus.SHCFiveCertificate.Generated
