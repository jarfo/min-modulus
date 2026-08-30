import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_02 : List ℕ := [17, 521, 261, 131, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1825, 3785, 2485, 1665, 4227, 1187, 1507, 2306, 524, 772, 4884, 2308, 20, 2468, 2633, 773, 217, 153, 5204, 589, 85, 2631, 837, 775, 774, 401, 642, 2466, 2478, 402, 465, 3344, 3024, 154, 403, 526, 525, 3185, 527, 5045, 155, 4544, 21, 4224, 3025, 643, 641, 2788, 2476, 4885, 2786, 2626, 4225, 77, 705, 93, 24, 22, 4397, 23, 961, 4237, 28, 898, 89, 385, 25, 387, 31, 4547, 12, 769, 4232, 897, 3906, 1907, 1667, 2808, 30, 771, 5824, 3747]

private theorem valid53_02 : ∀ code ∈ codes53_02, validRelationCode code := by
  decide

private theorem cover53_02 : ∀ q : IncreasingFourTail 51 (⟨2, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_02 (increasingFourValues (N := 53) ⟨⟨2, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a02
    (q : IncreasingFourTail 51 (⟨2, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨2, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_02 _ valid53_02 (cover53_02 q)

end MinModulus.SHCFiveCertificate.Generated
