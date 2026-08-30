import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_33 : List ℕ := [772]

private theorem valid39_33 : ∀ code ∈ codes39_33, validRelationCode code := by
  decide

private theorem cover39_33 : ∀ q : IncreasingFourTail 37 (⟨33, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_33 (increasingFourValues (N := 39) ⟨⟨33, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a33
    (q : IncreasingFourTail 37 (⟨33, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨33, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_33 _ valid39_33 (cover39_33 q)

end MinModulus.SHCFiveCertificate.Generated
