import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_07 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 772, 522, 4227, 2308, 18, 262, 153, 773, 4387, 4232, 2468, 523, 263, 19, 209, 713, 321, 2624, 10, 4884, 833, 2626, 642, 402, 4584, 2064, 2786, 2631, 643, 1347, 403, 2465, 1825, 1665, 589, 385, 85, 12, 449, 27, 3264, 20, 524, 386, 770, 525, 21, 13, 5665, 3907, 28, 24]

private theorem valid41_07 : ∀ code ∈ codes41_07, validRelationCode code := by
  decide

private theorem cover41_07 : ∀ q : IncreasingFourTail 39 (⟨7, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_07 (increasingFourValues (N := 41) ⟨⟨7, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a07
    (q : IncreasingFourTail 39 (⟨7, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨7, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_07 _ valid41_07 (cover41_07 q)

end MinModulus.SHCFiveCertificate.Generated
