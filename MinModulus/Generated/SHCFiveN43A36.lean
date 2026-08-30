import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_36 : List ℕ := [17, 402]

private theorem valid43_36 : ∀ code ∈ codes43_36, validRelationCode code := by
  decide

private theorem cover43_36 : ∀ q : IncreasingFourTail 41 (⟨36, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_36 (increasingFourValues (N := 43) ⟨⟨36, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a36
    (q : IncreasingFourTail 41 (⟨36, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨36, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_36 _ valid43_36 (cover43_36 q)

end MinModulus.SHCFiveCertificate.Generated
