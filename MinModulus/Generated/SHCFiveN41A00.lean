import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_00 : List ℕ := [1344]

private theorem valid41_00 : ∀ code ∈ codes41_00, validRelationCode code := by
  decide

private theorem cover41_00 : ∀ q : IncreasingFourTail 39 (⟨0, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_00 (increasingFourValues (N := 41) ⟨⟨0, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a00
    (q : IncreasingFourTail 39 (⟨0, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨0, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_00 _ valid41_00 (cover41_00 q)

end MinModulus.SHCFiveCertificate.Generated
