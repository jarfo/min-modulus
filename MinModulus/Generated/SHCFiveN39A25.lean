import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_25 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 403, 589, 2706]

private theorem valid39_25 : ∀ code ∈ codes39_25, validRelationCode code := by
  decide

private theorem cover39_25 : ∀ q : IncreasingFourTail 37 (⟨25, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_25 (increasingFourValues (N := 39) ⟨⟨25, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a25
    (q : IncreasingFourTail 37 (⟨25, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨25, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_25 _ valid39_25 (cover39_25 q)

end MinModulus.SHCFiveCertificate.Generated
