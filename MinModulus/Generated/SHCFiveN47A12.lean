import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_12 : List ℕ := [17, 521, 261, 131, 772, 402, 279, 278, 713, 4425, 4265, 4584, 589, 403, 153, 773, 4884, 642, 2626, 4227, 2308, 209, 85, 2465, 643, 2468, 4232, 4234, 2786, 1905, 518, 2305, 2631, 321, 4387, 2624, 10, 2064, 1186, 3746, 263, 385, 519, 2546, 1546, 3586, 770, 3757, 387, 2944, 3745, 5510, 3273, 193, 401, 5504, 4224, 386, 522, 262, 201, 1984, 3907, 1528, 28, 155, 1865, 1988, 21, 2545, 1507, 2067, 12, 26, 774, 22]

private theorem valid47_12 : ∀ code ∈ codes47_12, validRelationCode code := by
  decide

private theorem cover47_12 : ∀ q : IncreasingFourTail 45 (⟨12, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_12 (increasingFourValues (N := 47) ⟨⟨12, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a12
    (q : IncreasingFourTail 45 (⟨12, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨12, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_12 _ valid47_12 (cover47_12 q)

end MinModulus.SHCFiveCertificate.Generated
