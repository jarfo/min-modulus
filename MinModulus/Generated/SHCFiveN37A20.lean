import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_20 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 3264, 14, 77, 773, 4387, 15, 2485]

private theorem valid37_20 : ∀ code ∈ codes37_20, validRelationCode code := by
  decide

private theorem cover37_20 : ∀ q : IncreasingFourTail 35 (⟨20, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_20 (increasingFourValues (N := 37) ⟨⟨20, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a20
    (q : IncreasingFourTail 35 (⟨20, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨20, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_20 _ valid37_20 (cover37_20 q)

end MinModulus.SHCFiveCertificate.Generated
