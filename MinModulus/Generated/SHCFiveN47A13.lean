import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_13 : List ℕ := [17, 521, 261, 131, 1186, 772, 278, 4265, 4584, 402, 713, 279, 4425, 589, 403, 4884, 153, 773, 4227, 642, 2626, 2308, 85, 2631, 4387, 643, 4232, 2468, 11, 519, 2786, 10, 4234, 321, 518, 2305, 2624, 209, 1905, 2465, 3585, 193, 1865, 3745, 3586, 3746, 6, 833, 1984, 2545, 19, 1993, 2148, 522, 262, 2546, 897, 5036, 1187, 1988, 3273, 20, 28, 386, 154, 641, 770, 26, 22, 201, 385, 387, 27, 7]

private theorem valid47_13 : ∀ code ∈ codes47_13, validRelationCode code := by
  decide

private theorem cover47_13 : ∀ q : IncreasingFourTail 45 (⟨13, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_13 (increasingFourValues (N := 47) ⟨⟨13, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a13
    (q : IncreasingFourTail 45 (⟨13, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨13, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_13 _ valid47_13 (cover47_13 q)

end MinModulus.SHCFiveCertificate.Generated
