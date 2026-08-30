import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_18 : List ℕ := [1185]

private theorem valid39_18 : ∀ code ∈ codes39_18, validRelationCode code := by
  decide

private theorem cover39_18 : ∀ q : IncreasingFourTail 37 (⟨18, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_18 (increasingFourValues (N := 39) ⟨⟨18, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a18
    (q : IncreasingFourTail 37 (⟨18, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨18, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_18 _ valid39_18 (cover39_18 q)

end MinModulus.SHCFiveCertificate.Generated
