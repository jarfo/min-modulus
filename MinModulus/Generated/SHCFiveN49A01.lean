import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes49_01 : List ℕ := [17, 577, 18, 521, 337, 522, 261, 201, 262, 131, 19, 523, 263, 1825, 3785, 2485, 1665, 85, 4227, 401, 773, 2466, 2468, 772, 524, 217, 589, 642, 641, 4387, 4232, 2306, 2631, 2308, 2633, 20, 153, 525, 4397, 1187, 2628, 774, 643, 402, 2626, 4552, 4237, 2786, 837, 465, 2476, 2788, 2478, 21, 4234, 775, 403, 4547, 1347, 4225, 3907, 3185, 5045, 154, 155, 898, 93, 897, 385, 2954, 3946, 12, 386, 526, 89, 77, 769]

private theorem valid49_01 : ∀ code ∈ codes49_01, validRelationCode code := by
  decide

private theorem cover49_01 : ∀ q : IncreasingFourTail 47 (⟨1, by norm_num⟩ : Fin 44),
    coveredNat 49 codes49_01 (increasingFourValues (N := 49) ⟨⟨1, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate49_a01
    (q : IncreasingFourTail 47 (⟨1, by norm_num⟩ : Fin 44)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 49 (increasingFourValues (N := 49) ⟨⟨1, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 49 codes49_01 _ valid49_01 (cover49_01 q)

end MinModulus.SHCFiveCertificate.Generated
