import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_19 : List ℕ := [1185]

private theorem valid41_19 : ∀ code ∈ codes41_19, validRelationCode code := by
  decide

private theorem cover41_19 : ∀ q : IncreasingFourTail 39 (⟨19, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_19 (increasingFourValues (N := 41) ⟨⟨19, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a19
    (q : IncreasingFourTail 39 (⟨19, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨19, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_19 _ valid41_19 (cover41_19 q)

end MinModulus.SHCFiveCertificate.Generated
