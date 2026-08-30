import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_23 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 4227, 2308, 85, 589, 2631, 403, 643, 2786, 386, 93, 4387]

private theorem valid41_23 : ∀ code ∈ codes41_23, validRelationCode code := by
  decide

private theorem cover41_23 : ∀ q : IncreasingFourTail 39 (⟨23, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_23 (increasingFourValues (N := 41) ⟨⟨23, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a23
    (q : IncreasingFourTail 39 (⟨23, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨23, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_23 _ valid41_23 (cover41_23 q)

end MinModulus.SHCFiveCertificate.Generated
