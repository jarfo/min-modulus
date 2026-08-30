import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_30 : List ℕ := [17, 521, 261, 772]

private theorem valid39_30 : ∀ code ∈ codes39_30, validRelationCode code := by
  decide

private theorem cover39_30 : ∀ q : IncreasingFourTail 37 (⟨30, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_30 (increasingFourValues (N := 39) ⟨⟨30, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a30
    (q : IncreasingFourTail 37 (⟨30, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨30, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_30 _ valid39_30 (cover39_30 q)

end MinModulus.SHCFiveCertificate.Generated
