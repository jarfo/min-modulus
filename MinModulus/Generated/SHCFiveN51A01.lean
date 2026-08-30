import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_01 : List ℕ := [17, 577, 18, 521, 337, 522, 261, 201, 262, 131, 19, 523, 263, 1825, 3785, 2485, 1665, 85, 4227, 401, 773, 2466, 2468, 772, 524, 217, 589, 642, 641, 4387, 4232, 2306, 2631, 2308, 2633, 20, 153, 525, 4397, 1187, 2626, 402, 643, 2628, 774, 4552, 4237, 2788, 465, 837, 2478, 2786, 2476, 21, 4234, 403, 775, 4547, 154, 526, 5045, 3185, 4225, 4230, 3912, 770, 705, 3907, 1667, 93, 385, 1548, 2488, 386, 769, 29, 899, 4087, 1907, 24, 89, 77, 13, 4874, 5346]

private theorem valid51_01 : ∀ code ∈ codes51_01, validRelationCode code := by
  decide

private theorem cover51_01 : ∀ q : IncreasingFourTail 49 (⟨1, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_01 (increasingFourValues (N := 51) ⟨⟨1, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a01
    (q : IncreasingFourTail 49 (⟨1, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨1, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_01 _ valid51_01 (cover51_01 q)

end MinModulus.SHCFiveCertificate.Generated
