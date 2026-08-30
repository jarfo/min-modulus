import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_19 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 3585, 772, 4227, 2308, 773, 2468, 3745, 1865, 2545, 4387, 4232, 642, 402, 153, 2626, 2631, 85, 589, 2786, 643, 4884, 403, 1347, 209, 5025, 321, 10, 713, 1827, 1868, 386, 518, 385, 2624, 898, 833, 1905, 1667, 4425, 770, 278, 526, 449, 705, 279, 519]

private theorem valid49_19 : ∀ code ∈ codes49_19, validRelationCode code := by
  decide

private theorem cover49_19 : ∀ q : IncreasingFourTail 47 (⟨19, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_19 (increasingFourValues (N := 49) ⟨⟨19, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a19
    (q : IncreasingFourTail 47 (⟨19, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨19, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_19 _ valid49_19 (cover49_19 q)

end MinModulus.SHCFiveCertificate.Generated
