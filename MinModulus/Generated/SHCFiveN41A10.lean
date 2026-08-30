import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_10 : List ℕ := [17, 521, 261, 131, 772, 402, 279, 278, 713, 4425, 4265, 4584, 589, 403, 153, 773, 4884, 642, 2626, 4227, 2308, 85, 209, 2465, 643, 321, 2305, 518, 2468, 1905, 2631, 4387, 10, 4232, 2786, 2624, 4234, 385, 519, 2064, 263, 3586, 387, 770, 3585, 2546, 386, 262, 337, 522, 193, 523, 5504, 28, 201]

private theorem valid41_10 : ∀ code ∈ codes41_10, validRelationCode code := by
  decide

private theorem cover41_10 : ∀ q : IncreasingFourTail 39 (⟨10, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_10 (increasingFourValues (N := 41) ⟨⟨10, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a10
    (q : IncreasingFourTail 39 (⟨10, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨10, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_10 _ valid41_10 (cover41_10 q)

end MinModulus.SHCFiveCertificate.Generated
