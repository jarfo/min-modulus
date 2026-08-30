import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_18 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 4227, 2308, 642, 2626, 209, 713, 321, 1905, 4425, 2465, 2064, 4584, 2624, 153, 773, 4387, 4232, 2468, 643, 403, 2786, 589, 85, 2631, 518, 2305, 4265, 10, 278, 1984, 193, 519, 4884, 4234, 1506, 1187, 1668, 11, 23, 26, 4876, 3268, 3585, 30, 279, 3273, 12, 201, 3344, 2944, 1665, 3746, 262, 22, 449, 77, 771]

private theorem valid51_18 : ∀ code ∈ codes51_18, validRelationCode code := by
  decide

private theorem cover51_18 : ∀ q : IncreasingFourTail 49 (⟨18, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_18 (increasingFourValues (N := 51) ⟨⟨18, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a18
    (q : IncreasingFourTail 49 (⟨18, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨18, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_18 _ valid51_18 (cover51_18 q)

end MinModulus.SHCFiveCertificate.Generated
