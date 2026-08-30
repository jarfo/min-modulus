import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_22 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308]

private theorem valid37_22 : ∀ code ∈ codes37_22, validRelationCode code := by
  decide

private theorem cover37_22 : ∀ q : IncreasingFourTail 35 (⟨22, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_22 (increasingFourValues (N := 37) ⟨⟨22, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a22
    (q : IncreasingFourTail 35 (⟨22, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨22, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_22 _ valid37_22 (cover37_22 q)

end MinModulus.SHCFiveCertificate.Generated
