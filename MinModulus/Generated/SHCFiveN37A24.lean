import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_24 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 85, 77, 386, 770]

private theorem valid37_24 : ∀ code ∈ codes37_24, validRelationCode code := by
  decide

private theorem cover37_24 : ∀ q : IncreasingFourTail 35 (⟨24, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_24 (increasingFourValues (N := 37) ⟨⟨24, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a24
    (q : IncreasingFourTail 35 (⟨24, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨24, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_24 _ valid37_24 (cover37_24 q)

end MinModulus.SHCFiveCertificate.Generated
