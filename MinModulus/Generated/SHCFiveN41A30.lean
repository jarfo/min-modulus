import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_30 : List ℕ := [17, 521, 261, 131, 772, 402]

private theorem valid41_30 : ∀ code ∈ codes41_30, validRelationCode code := by
  decide

private theorem cover41_30 : ∀ q : IncreasingFourTail 39 (⟨30, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_30 (increasingFourValues (N := 41) ⟨⟨30, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a30
    (q : IncreasingFourTail 39 (⟨30, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨30, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_30 _ valid41_30 (cover41_30 q)

end MinModulus.SHCFiveCertificate.Generated
