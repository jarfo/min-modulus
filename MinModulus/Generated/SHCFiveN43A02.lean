import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_02 : List ℕ := [17, 521, 261, 131, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1825, 3785, 2485, 1665, 4227, 1187, 1507, 2308, 772, 524, 2306, 20, 2631, 85, 2466, 4884, 2633, 2476, 217, 589, 153, 837, 773, 5204, 21, 401, 774, 465, 3344, 402, 642, 705, 4397, 641, 12, 2626, 526, 154, 403, 775, 4544, 24, 77, 643, 2478, 833, 385, 25]

private theorem valid43_02 : ∀ code ∈ codes43_02, validRelationCode code := by
  decide

private theorem cover43_02 : ∀ q : IncreasingFourTail 41 (⟨2, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_02 (increasingFourValues (N := 43) ⟨⟨2, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a02
    (q : IncreasingFourTail 41 (⟨2, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨2, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_02 _ valid43_02 (cover43_02 q)

end MinModulus.SHCFiveCertificate.Generated
