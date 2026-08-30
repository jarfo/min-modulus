import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_22 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 386, 403, 643, 773, 4387, 770, 2954, 3907]

private theorem valid41_22 : ∀ code ∈ codes41_22, validRelationCode code := by
  decide

private theorem cover41_22 : ∀ q : IncreasingFourTail 39 (⟨22, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_22 (increasingFourValues (N := 41) ⟨⟨22, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a22
    (q : IncreasingFourTail 39 (⟨22, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨22, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_22 _ valid41_22 (cover41_22 q)

end MinModulus.SHCFiveCertificate.Generated
