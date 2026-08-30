import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_31 : List ℕ := [17, 521, 261, 131, 772, 642, 2626]

private theorem valid43_31 : ∀ code ∈ codes43_31, validRelationCode code := by
  decide

private theorem cover43_31 : ∀ q : IncreasingFourTail 41 (⟨31, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_31 (increasingFourValues (N := 43) ⟨⟨31, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a31
    (q : IncreasingFourTail 41 (⟨31, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨31, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_31 _ valid43_31 (cover43_31 q)

end MinModulus.SHCFiveCertificate.Generated
