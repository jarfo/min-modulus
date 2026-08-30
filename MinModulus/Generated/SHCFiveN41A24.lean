import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_24 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 77, 2631, 3911, 153, 773]

private theorem valid41_24 : ∀ code ∈ codes41_24, validRelationCode code := by
  decide

private theorem cover41_24 : ∀ q : IncreasingFourTail 39 (⟨24, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_24 (increasingFourValues (N := 41) ⟨⟨24, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a24
    (q : IncreasingFourTail 39 (⟨24, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨24, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_24 _ valid41_24 (cover41_24 q)

end MinModulus.SHCFiveCertificate.Generated
