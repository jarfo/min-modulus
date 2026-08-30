import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_11 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 403, 589, 4387, 4227, 4232, 2786, 2631, 2308, 85, 153, 773, 643, 1347, 2468, 4884, 4234, 2024, 2704, 3904, 209, 519, 321, 4425, 1825, 2546, 713, 1905, 3746, 10, 201, 2624, 2305, 518, 337, 577, 2465, 4265, 4584, 278, 3765, 262, 2064, 1665, 522, 18, 3586, 1988, 385, 27, 2944, 770, 4552, 3428, 217, 401, 3907, 386, 93, 4224, 3585, 3906, 1527, 3185, 12, 193, 89, 525, 387, 771, 3757, 524, 898, 526, 837, 13, 29, 5504]

private theorem valid49_11 : ∀ code ∈ codes49_11, validRelationCode code := by
  decide

private theorem cover49_11 : ∀ q : IncreasingFourTail 47 (⟨11, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_11 (increasingFourValues (N := 49) ⟨⟨11, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a11
    (q : IncreasingFourTail 47 (⟨11, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨11, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_11 _ valid49_11 (cover49_11 q)

end MinModulus.SHCFiveCertificate.Generated
