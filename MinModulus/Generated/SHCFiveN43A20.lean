import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_20 : List ℕ := [1185]

private theorem valid43_20 : ∀ code ∈ codes43_20, validRelationCode code := by
  decide

private theorem cover43_20 : ∀ q : IncreasingFourTail 41 (⟨20, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_20 (increasingFourValues (N := 43) ⟨⟨20, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a20
    (q : IncreasingFourTail 41 (⟨20, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨20, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_20 _ valid43_20 (cover43_20 q)

end MinModulus.SHCFiveCertificate.Generated
