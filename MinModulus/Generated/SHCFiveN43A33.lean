import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_33 : List ℕ := [17, 521, 261, 131, 772]

private theorem valid43_33 : ∀ code ∈ codes43_33, validRelationCode code := by
  decide

private theorem cover43_33 : ∀ q : IncreasingFourTail 41 (⟨33, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_33 (increasingFourValues (N := 43) ⟨⟨33, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a33
    (q : IncreasingFourTail 41 (⟨33, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨33, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_33 _ valid43_33 (cover43_33 q)

end MinModulus.SHCFiveCertificate.Generated
