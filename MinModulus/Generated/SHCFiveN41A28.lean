import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_28 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 85, 77, 386, 770]

private theorem valid41_28 : ∀ code ∈ codes41_28, validRelationCode code := by
  decide

private theorem cover41_28 : ∀ q : IncreasingFourTail 39 (⟨28, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_28 (increasingFourValues (N := 41) ⟨⟨28, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a28
    (q : IncreasingFourTail 39 (⟨28, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨28, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_28 _ valid41_28 (cover41_28 q)

end MinModulus.SHCFiveCertificate.Generated
