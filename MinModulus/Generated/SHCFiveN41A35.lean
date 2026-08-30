import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_35 : List ℕ := [772]

private theorem valid41_35 : ∀ code ∈ codes41_35, validRelationCode code := by
  decide

private theorem cover41_35 : ∀ q : IncreasingFourTail 39 (⟨35, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_35 (increasingFourValues (N := 41) ⟨⟨35, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a35
    (q : IncreasingFourTail 39 (⟨35, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨35, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_35 _ valid41_35 (cover41_35 q)

end MinModulus.SHCFiveCertificate.Generated
