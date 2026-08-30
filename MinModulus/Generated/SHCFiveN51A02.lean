import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes51_02 : List ℕ := [17, 521, 261, 131, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1825, 3785, 2485, 1665, 4227, 1187, 1507, 2308, 2306, 2631, 2466, 524, 772, 4884, 20, 85, 4224, 153, 773, 642, 641, 643, 21, 2626, 5204, 4544, 774, 217, 2476, 775, 837, 589, 154, 402, 4552, 705, 155, 401, 2468, 3344, 4397, 465, 385, 5045, 403, 526, 4885, 3024, 25, 4225, 2786, 2633, 5184, 22, 897, 769, 5504, 4234, 30, 29, 5824, 2478, 4385, 961, 89, 77, 899, 31, 4387, 24, 28, 833, 387, 771, 23, 4864]

private theorem valid51_02 : ∀ code ∈ codes51_02, validRelationCode code := by
  decide

private theorem cover51_02 : ∀ q : IncreasingFourTail 49 (⟨2, by norm_num⟩ : Fin 46),
    coveredNat 51 codes51_02 (increasingFourValues (N := 51) ⟨⟨2, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate51_a02
    (q : IncreasingFourTail 49 (⟨2, by norm_num⟩ : Fin 46)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 51 (increasingFourValues (N := 51) ⟨⟨2, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 51 codes51_02 _ valid51_02 (cover51_02 q)

end MinModulus.SHCFiveCertificate.Generated
