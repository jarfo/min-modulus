import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_25 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 85, 153, 773, 643, 402, 4227, 386, 770, 1667]

private theorem valid41_25 : ∀ code ∈ codes41_25, validRelationCode code := by
  decide

private theorem cover41_25 : ∀ q : IncreasingFourTail 39 (⟨25, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_25 (increasingFourValues (N := 41) ⟨⟨25, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a25
    (q : IncreasingFourTail 39 (⟨25, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨25, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_25 _ valid41_25 (cover41_25 q)

end MinModulus.SHCFiveCertificate.Generated
