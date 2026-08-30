import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_24 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 386, 403, 643, 773, 4387, 770, 2954, 3907]

private theorem valid43_24 : ∀ code ∈ codes43_24, validRelationCode code := by
  decide

private theorem cover43_24 : ∀ q : IncreasingFourTail 41 (⟨24, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_24 (increasingFourValues (N := 43) ⟨⟨24, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a24
    (q : IncreasingFourTail 41 (⟨24, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨24, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_24 _ valid43_24 (cover43_24 q)

end MinModulus.SHCFiveCertificate.Generated
