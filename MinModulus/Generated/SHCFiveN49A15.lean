import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_15 : List ℕ := [17, 521, 261, 131, 1186, 772, 4584, 278, 402, 713, 589, 403, 279, 153, 773, 4884, 321, 209, 2626, 642, 2624, 518, 4227, 2308, 643, 2631, 4387, 2468, 85, 4232, 2786, 10, 2064, 519, 4234, 193, 1984, 18, 262, 577, 6, 3757, 1527, 201, 337, 2546, 522, 833, 385, 5036, 3904, 3273, 263, 1827, 1837, 523, 4870, 2704, 465, 1667, 770, 93, 897, 20, 524, 386, 526, 705, 387, 5184]

private theorem valid49_15 : ∀ code ∈ codes49_15, validRelationCode code := by
  decide

private theorem cover49_15 : ∀ q : IncreasingFourTail 47 (⟨15, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_15 (increasingFourValues (N := 49) ⟨⟨15, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a15
    (q : IncreasingFourTail 47 (⟨15, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨15, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_15 _ valid49_15 (cover49_15 q)

end MinModulus.SHCFiveCertificate.Generated
