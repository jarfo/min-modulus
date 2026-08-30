import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_25 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 4227, 2308, 85, 589, 2631, 403, 643, 2786, 386, 93, 4387]

private theorem valid43_25 : ∀ code ∈ codes43_25, validRelationCode code := by
  decide

private theorem cover43_25 : ∀ q : IncreasingFourTail 41 (⟨25, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_25 (increasingFourValues (N := 43) ⟨⟨25, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a25
    (q : IncreasingFourTail 41 (⟨25, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨25, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_25 _ valid43_25 (cover43_25 q)

end MinModulus.SHCFiveCertificate.Generated
