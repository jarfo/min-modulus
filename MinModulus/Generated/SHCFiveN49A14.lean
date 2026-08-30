import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_14 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 278, 279, 4425, 4584, 153, 773, 589, 403, 4884, 642, 4227, 2308, 2626, 85, 2631, 4387, 643, 4232, 2468, 10, 2786, 518, 11, 519, 321, 4234, 1905, 209, 2624, 19, 2465, 193, 1865, 3745, 263, 2064, 1984, 523, 2545, 5184, 4876, 1187, 3268, 6, 2148, 26, 18, 262, 641, 27, 775, 2028, 522, 1993, 386, 154, 770, 774, 837, 527, 5504, 1837, 2788, 2478, 22, 14, 961, 337, 93]

private theorem valid49_14 : ∀ code ∈ codes49_14, validRelationCode code := by
  decide

private theorem cover49_14 : ∀ q : IncreasingFourTail 47 (⟨14, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_14 (increasingFourValues (N := 49) ⟨⟨14, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a14
    (q : IncreasingFourTail 47 (⟨14, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨14, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_14 _ valid49_14 (cover49_14 q)

end MinModulus.SHCFiveCertificate.Generated
