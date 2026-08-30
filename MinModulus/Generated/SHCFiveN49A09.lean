import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_09 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 772, 4227, 2308, 18, 522, 262, 153, 773, 4387, 4232, 2468, 523, 263, 19, 402, 642, 1825, 2626, 1665, 2786, 643, 403, 2631, 589, 85, 4234, 4884, 1347, 209, 321, 713, 2624, 4425, 2465, 1905, 4584, 2064, 3757, 385, 2546, 3746, 1186, 1837, 12, 10, 2305, 1586, 4106, 20, 524, 3586, 833, 1187, 386, 2944, 518, 2954, 4066, 3946, 387, 3264, 278, 2866, 774, 897, 155, 775, 3765, 4265, 4547, 89, 641, 4385, 5505, 770, 771, 5204, 3105]

private theorem valid49_09 : ∀ code ∈ codes49_09, validRelationCode code := by
  decide

private theorem cover49_09 : ∀ q : IncreasingFourTail 47 (⟨9, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_09 (increasingFourValues (N := 49) ⟨⟨9, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a09
    (q : IncreasingFourTail 47 (⟨9, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨9, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_09 _ valid49_09 (cover49_09 q)

end MinModulus.SHCFiveCertificate.Generated
