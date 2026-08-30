import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_37 : List ℕ := [772]

private theorem valid43_37 : ∀ code ∈ codes43_37, validRelationCode code := by
  decide

private theorem cover43_37 : ∀ q : IncreasingFourTail 41 (⟨37, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_37 (increasingFourValues (N := 43) ⟨⟨37, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a37
    (q : IncreasingFourTail 41 (⟨37, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨37, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_37 _ valid43_37 (cover43_37 q)

end MinModulus.SHCFiveCertificate.Generated
