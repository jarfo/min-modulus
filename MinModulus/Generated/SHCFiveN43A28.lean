import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_28 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308]

private theorem valid43_28 : ∀ code ∈ codes43_28, validRelationCode code := by
  decide

private theorem cover43_28 : ∀ q : IncreasingFourTail 41 (⟨28, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_28 (increasingFourValues (N := 43) ⟨⟨28, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a28
    (q : IncreasingFourTail 41 (⟨28, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨28, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_28 _ valid43_28 (cover43_28 q)

end MinModulus.SHCFiveCertificate.Generated
