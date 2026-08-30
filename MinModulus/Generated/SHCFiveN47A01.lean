import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_01 : List ℕ := [17, 577, 18, 521, 337, 522, 261, 201, 262, 131, 19, 523, 263, 1825, 3785, 2485, 1665, 85, 4227, 401, 773, 2466, 2468, 772, 524, 217, 589, 642, 641, 4387, 4232, 2306, 2631, 2308, 2633, 20, 153, 525, 4397, 1187, 2626, 402, 643, 2628, 774, 4552, 4237, 2788, 465, 837, 2478, 2786, 4234, 21, 2476, 403, 775, 4547, 23, 4225, 93, 4230, 24, 28, 898, 770, 26, 89, 77, 897, 13, 387, 4874]

private theorem valid47_01 : ∀ code ∈ codes47_01, validRelationCode code := by
  decide

private theorem cover47_01 : ∀ q : IncreasingFourTail 45 (⟨1, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_01 (increasingFourValues (N := 47) ⟨⟨1, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a01
    (q : IncreasingFourTail 45 (⟨1, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨1, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_01 _ valid47_01 (cover47_01 q)

end MinModulus.SHCFiveCertificate.Generated
