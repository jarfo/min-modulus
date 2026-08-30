import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_34 : List ℕ := [17, 521, 261, 772]

private theorem valid43_34 : ∀ code ∈ codes43_34, validRelationCode code := by
  decide

private theorem cover43_34 : ∀ q : IncreasingFourTail 41 (⟨34, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_34 (increasingFourValues (N := 43) ⟨⟨34, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a34
    (q : IncreasingFourTail 41 (⟨34, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨34, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_34 _ valid43_34 (cover43_34 q)

end MinModulus.SHCFiveCertificate.Generated
