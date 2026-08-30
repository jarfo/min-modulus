import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_27 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 403, 589, 2706]

private theorem valid41_27 : ∀ code ∈ codes41_27, validRelationCode code := by
  decide

private theorem cover41_27 : ∀ q : IncreasingFourTail 39 (⟨27, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_27 (increasingFourValues (N := 41) ⟨⟨27, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a27
    (q : IncreasingFourTail 39 (⟨27, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨27, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_27 _ valid41_27 (cover41_27 q)

end MinModulus.SHCFiveCertificate.Generated
