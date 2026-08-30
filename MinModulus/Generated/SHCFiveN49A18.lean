import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_18 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 772, 4227, 2308, 402, 642, 2626, 153, 773, 4884, 4232, 589, 2468, 4387, 2631, 85, 643, 2786, 403, 1507, 4234, 3585, 4876, 518, 3268, 1905, 1827, 1828, 321, 278, 713, 193, 2465, 10, 4425, 209, 1667, 2624, 1865, 4265, 385, 2476, 465, 705, 13, 11, 519, 898, 526, 3745, 3586, 3273]

private theorem valid49_18 : ∀ code ∈ codes49_18, validRelationCode code := by
  decide

private theorem cover49_18 : ∀ q : IncreasingFourTail 47 (⟨18, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_18 (increasingFourValues (N := 49) ⟨⟨18, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a18
    (q : IncreasingFourTail 47 (⟨18, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨18, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_18 _ valid49_18 (cover49_18 q)

end MinModulus.SHCFiveCertificate.Generated
