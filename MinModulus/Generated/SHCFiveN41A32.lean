import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_32 : List ℕ := [17, 521, 261, 772]

private theorem valid41_32 : ∀ code ∈ codes41_32, validRelationCode code := by
  decide

private theorem cover41_32 : ∀ q : IncreasingFourTail 39 (⟨32, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_32 (increasingFourValues (N := 41) ⟨⟨32, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a32
    (q : IncreasingFourTail 39 (⟨32, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨32, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_32 _ valid41_32 (cover41_32 q)

end MinModulus.SHCFiveCertificate.Generated
