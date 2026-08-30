import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_01 : List ℕ := [17, 577, 18, 521, 337, 522, 261, 201, 262, 131, 19, 523, 263, 1825, 3785, 2485, 1665, 85, 4227, 401, 773, 2466, 2468, 772, 524, 217, 589, 642, 641, 4387, 4232, 2306, 2631, 2308, 2633, 20, 153, 525, 4397, 1187, 2628, 774, 643, 402, 2626, 4552, 4237, 2786, 837, 465, 2476, 2788, 2478, 21, 4234, 775, 403, 4547, 1347, 4225, 5045, 3185, 154, 526, 770, 705, 385, 77, 4707, 1667, 3912, 3747, 3907, 89, 1827, 24, 1528, 12, 897, 769, 25, 13, 387, 155, 28, 898, 386, 93, 29, 899, 5514]

private theorem valid53_01 : ∀ code ∈ codes53_01, validRelationCode code := by
  decide

private theorem cover53_01 : ∀ q : IncreasingFourTail 51 (⟨1, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_01 (increasingFourValues (N := 53) ⟨⟨1, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a01
    (q : IncreasingFourTail 51 (⟨1, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨1, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_01 _ valid53_01 (cover53_01 q)

end MinModulus.SHCFiveCertificate.Generated
