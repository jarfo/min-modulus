import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_31 : List ℕ := [17, 521, 261, 131, 772]

private theorem valid41_31 : ∀ code ∈ codes41_31, validRelationCode code := by
  decide

private theorem cover41_31 : ∀ q : IncreasingFourTail 39 (⟨31, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_31 (increasingFourValues (N := 41) ⟨⟨31, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a31
    (q : IncreasingFourTail 39 (⟨31, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨31, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_31 _ valid41_31 (cover41_31 q)

end MinModulus.SHCFiveCertificate.Generated
