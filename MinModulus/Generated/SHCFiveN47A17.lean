import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_17 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 772, 4227, 2308, 153, 773, 402, 4232, 2468, 642, 2626, 4387, 2631, 589, 2786, 85, 643, 403, 4884, 1347, 4234, 3428, 11, 279, 10, 519, 1346, 27, 527, 1668, 278, 23, 518, 321, 385, 4870, 22, 2465, 1667, 12, 13, 2624, 2305, 770, 526, 705, 713, 77, 898, 14, 1984, 1905]

private theorem valid47_17 : ∀ code ∈ codes47_17, validRelationCode code := by
  decide

private theorem cover47_17 : ∀ q : IncreasingFourTail 45 (⟨17, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_17 (increasingFourValues (N := 47) ⟨⟨17, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a17
    (q : IncreasingFourTail 45 (⟨17, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨17, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_17 _ valid47_17 (cover47_17 q)

end MinModulus.SHCFiveCertificate.Generated
