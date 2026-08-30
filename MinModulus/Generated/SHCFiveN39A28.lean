import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_28 : List ℕ := [17, 521, 261, 131, 772, 402]

private theorem valid39_28 : ∀ code ∈ codes39_28, validRelationCode code := by
  decide

private theorem cover39_28 : ∀ q : IncreasingFourTail 37 (⟨28, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_28 (increasingFourValues (N := 39) ⟨⟨28, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a28
    (q : IncreasingFourTail 37 (⟨28, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨28, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_28 _ valid39_28 (cover39_28 q)

end MinModulus.SHCFiveCertificate.Generated
