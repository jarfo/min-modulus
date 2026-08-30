import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_02 : List ℕ := [17, 521, 261, 131, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1825, 3785, 2485, 1665, 4227, 1187, 1507, 2308, 772, 524, 2306, 20, 4884, 2631, 2466, 85, 4224, 153, 589, 773, 217, 642, 5204, 21, 774, 837, 643, 775, 154, 2626, 641, 2476, 4544, 705, 4234, 22, 769, 25, 24, 4225, 465, 4385, 4547, 89, 1667, 833, 3344, 4397, 5045, 961, 4230, 1828, 1993, 29, 403, 5184, 1992, 402, 26, 385]

private theorem valid47_02 : ∀ code ∈ codes47_02, validRelationCode code := by
  decide

private theorem cover47_02 : ∀ q : IncreasingFourTail 45 (⟨2, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_02 (increasingFourValues (N := 47) ⟨⟨2, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a02
    (q : IncreasingFourTail 45 (⟨2, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨2, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_02 _ valid47_02 (cover47_02 q)

end MinModulus.SHCFiveCertificate.Generated
