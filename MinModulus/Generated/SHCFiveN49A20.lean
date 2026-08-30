import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_20 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 3585, 3745, 1865, 2545, 4227, 772, 2308, 773, 2468, 4387, 4232, 153, 4884, 85, 642, 2626, 2465, 402, 589, 1905, 2476, 2631, 465, 3344, 321, 705, 209, 713, 4544, 2624, 4584, 526, 22, 2305, 4066, 770, 2954]

private theorem valid49_20 : ∀ code ∈ codes49_20, validRelationCode code := by
  decide

private theorem cover49_20 : ∀ q : IncreasingFourTail 47 (⟨20, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_20 (increasingFourValues (N := 49) ⟨⟨20, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a20
    (q : IncreasingFourTail 47 (⟨20, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨20, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_20 _ valid49_20 (cover49_20 q)

end MinModulus.SHCFiveCertificate.Generated
