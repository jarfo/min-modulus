import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_17 : List ℕ := [17, 521, 261, 131, 1186, 772, 4584, 4265, 278, 402, 713, 4425, 589, 403, 279, 4884, 153, 773, 4227, 2308, 2468, 4232, 4387, 2626, 642, 10, 518, 321, 209, 1905, 519, 2305, 2786, 643, 2631, 2465, 85, 11, 193, 2624, 1984, 1825, 6, 1546, 4234, 1527, 1347, 2064, 5184, 1668, 385, 4544, 5025, 1667, 12, 262, 1187, 26, 1865, 1827, 1837, 18, 201, 217, 31, 3745, 770, 522, 833, 263]

private theorem valid51_17 : ∀ code ∈ codes51_17, validRelationCode code := by
  decide

private theorem cover51_17 : ∀ q : IncreasingFourTail 49 (⟨17, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_17 (increasingFourValues (N := 51) ⟨⟨17, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a17
    (q : IncreasingFourTail 49 (⟨17, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨17, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_17 _ valid51_17 (cover51_17 q)

end MinModulus.SHCFiveCertificate.Generated
