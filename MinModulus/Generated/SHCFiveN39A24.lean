import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_24 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308]

private theorem valid39_24 : ∀ code ∈ codes39_24, validRelationCode code := by
  decide

private theorem cover39_24 : ∀ q : IncreasingFourTail 37 (⟨24, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_24 (increasingFourValues (N := 39) ⟨⟨24, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a24
    (q : IncreasingFourTail 37 (⟨24, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨24, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_24 _ valid39_24 (cover39_24 q)

end MinModulus.SHCFiveCertificate.Generated
