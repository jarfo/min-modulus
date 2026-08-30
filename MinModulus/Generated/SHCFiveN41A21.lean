import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_21 : List ℕ := [17, 521, 261, 131, 3785, 2485, 4227, 772, 2308, 85, 642, 643, 589, 2631, 403, 2786, 402, 2626, 3906, 386, 2706, 1346, 526, 3344]

private theorem valid41_21 : ∀ code ∈ codes41_21, validRelationCode code := by
  decide

private theorem cover41_21 : ∀ q : IncreasingFourTail 39 (⟨21, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_21 (increasingFourValues (N := 41) ⟨⟨21, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a21
    (q : IncreasingFourTail 39 (⟨21, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨21, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_21 _ valid41_21 (cover41_21 q)

end MinModulus.SHCFiveCertificate.Generated
