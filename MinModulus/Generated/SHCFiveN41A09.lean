import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_09 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 1347, 402, 4227, 2308, 10, 2305, 278, 518, 4265, 11, 2624, 85, 153, 279, 2786, 2631, 2465, 321, 773, 4387, 4425, 589, 519, 643, 1825, 209, 713, 1905, 4232, 403, 2468, 337, 201, 3904, 577, 3586, 1988, 522, 4584, 262, 4224, 3765, 3746, 2064, 1665, 5191, 386, 4884, 4066, 2466, 401]

private theorem valid41_09 : ∀ code ∈ codes41_09, validRelationCode code := by
  decide

private theorem cover41_09 : ∀ q : IncreasingFourTail 39 (⟨9, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_09 (increasingFourValues (N := 41) ⟨⟨9, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a09
    (q : IncreasingFourTail 39 (⟨9, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨9, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_09 _ valid41_09 (cover41_09 q)

end MinModulus.SHCFiveCertificate.Generated
