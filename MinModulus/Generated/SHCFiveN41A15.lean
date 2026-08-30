import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_15 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 772, 4227, 2308, 10, 278, 518, 402, 642, 2626, 3585, 4265, 2305, 4387, 4232, 3757, 209, 2786, 403, 3746, 321, 1346, 1865, 2545, 713, 526, 2631, 589, 3344, 4425, 386, 85, 385, 4544, 449, 279]

private theorem valid41_15 : ∀ code ∈ codes41_15, validRelationCode code := by
  decide

private theorem cover41_15 : ∀ q : IncreasingFourTail 39 (⟨15, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_15 (increasingFourValues (N := 41) ⟨⟨15, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a15
    (q : IncreasingFourTail 39 (⟨15, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨15, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_15 _ valid41_15 (cover41_15 q)

end MinModulus.SHCFiveCertificate.Generated
