import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_20 : List ℕ := [17, 521, 261, 131, 3785, 2485, 642, 4227, 589, 773, 2631, 2468, 772, 402, 465, 4884, 526, 153, 403, 4885, 3786, 4234, 2786]

private theorem valid41_20 : ∀ code ∈ codes41_20, validRelationCode code := by
  decide

private theorem cover41_20 : ∀ q : IncreasingFourTail 39 (⟨20, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_20 (increasingFourValues (N := 41) ⟨⟨20, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a20
    (q : IncreasingFourTail 39 (⟨20, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨20, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_20 _ valid41_20 (cover41_20 q)

end MinModulus.SHCFiveCertificate.Generated
