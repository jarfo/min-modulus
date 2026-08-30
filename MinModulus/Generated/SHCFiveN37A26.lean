import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_26 : List ℕ := [17, 521, 261, 131, 772, 402]

private theorem valid37_26 : ∀ code ∈ codes37_26, validRelationCode code := by
  decide

private theorem cover37_26 : ∀ q : IncreasingFourTail 35 (⟨26, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_26 (increasingFourValues (N := 37) ⟨⟨26, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a26
    (q : IncreasingFourTail 35 (⟨26, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨26, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_26 _ valid37_26 (cover37_26 q)

end MinModulus.SHCFiveCertificate.Generated
