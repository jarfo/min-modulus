import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes41_13 : List ℕ := [17, 521, 261, 131, 1186, 772, 4584, 4265, 278, 402, 713, 4425, 589, 403, 279, 153, 773, 4884, 2546, 1868, 4227, 2308, 2624, 2626, 4232, 642, 85, 4387, 10, 11, 2465, 2305, 209, 2631, 833, 321, 2786, 2468, 643, 1187, 1905, 518, 1827, 201, 527, 12, 30, 89]

private theorem valid41_13 : ∀ code ∈ codes41_13, validRelationCode code := by
  decide

private theorem cover41_13 : ∀ q : IncreasingFourTail 39 (⟨13, by norm_num⟩ : Fin 36),
    coveredNat 41 codes41_13 (increasingFourValues (N := 41) ⟨⟨13, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate41_a13
    (q : IncreasingFourTail 39 (⟨13, by norm_num⟩ : Fin 36)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 41 (increasingFourValues (N := 41) ⟨⟨13, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 41 codes41_13 _ valid41_13 (cover41_13 q)

end MinModulus.SHCFiveCertificate.Generated
