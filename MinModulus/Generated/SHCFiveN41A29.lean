import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_29 : List ℕ := [17, 521, 261, 131, 772, 642, 2626]

private theorem valid41_29 : ∀ code ∈ codes41_29, validRelationCode code := by
  decide

private theorem cover41_29 : ∀ q : IncreasingFourTail 39 (⟨29, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_29 (increasingFourValues (N := 41) ⟨⟨29, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a29
    (q : IncreasingFourTail 39 (⟨29, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨29, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_29 _ valid41_29 (cover41_29 q)

end MinModulus.SHCFiveCertificate.Generated
