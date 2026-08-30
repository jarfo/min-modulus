import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_32 : List ℕ := [17, 521, 261, 131, 772, 402]

private theorem valid43_32 : ∀ code ∈ codes43_32, validRelationCode code := by
  decide

private theorem cover43_32 : ∀ q : IncreasingFourTail 41 (⟨32, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_32 (increasingFourValues (N := 43) ⟨⟨32, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a32
    (q : IncreasingFourTail 41 (⟨32, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨32, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_32 _ valid43_32 (cover43_32 q)

end MinModulus.SHCFiveCertificate.Generated
