import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_17 : List ℕ := [17, 521, 261, 131, 1186, 772, 4227, 2308, 1347, 2624, 2305, 2626, 10, 321, 2465, 2786, 2631, 11, 2468, 642, 402, 773, 4387, 589, 4232, 713, 518, 1905, 209, 643, 4425, 4265, 278, 403, 4584, 153, 4884, 85, 519, 279, 1346, 2064, 1984, 3428, 4234, 1825, 1187, 387, 465, 3745, 5036, 386, 30, 193, 201, 3757, 2808, 526, 15]

private theorem valid49_17 : ∀ code ∈ codes49_17, validRelationCode code := by
  decide

private theorem cover49_17 : ∀ q : IncreasingFourTail 47 (⟨17, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_17 (increasingFourValues (N := 49) ⟨⟨17, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a17
    (q : IncreasingFourTail 47 (⟨17, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨17, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_17 _ valid49_17 (cover49_17 q)

end MinModulus.SHCFiveCertificate.Generated
