import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_26 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308]

private theorem valid41_26 : ∀ code ∈ codes41_26, validRelationCode code := by
  decide

private theorem cover41_26 : ∀ q : IncreasingFourTail 39 (⟨26, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_26 (increasingFourValues (N := 41) ⟨⟨26, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a26
    (q : IncreasingFourTail 39 (⟨26, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨26, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_26 _ valid41_26 (cover41_26 q)

end MinModulus.SHCFiveCertificate.Generated
