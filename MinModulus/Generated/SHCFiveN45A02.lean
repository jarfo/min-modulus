import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_02 : List ℕ := [17, 521, 261, 131, 2024, 201, 262, 263, 2704, 337, 522, 523, 3904, 577, 18, 19, 1825, 3785, 2485, 1665, 4227, 1187, 1507, 2306, 524, 4884, 772, 2308, 20, 773, 2468, 5204, 774, 153, 217, 154, 775, 589, 3344, 3024, 401, 402, 403, 526, 525, 465, 837, 3185, 5045, 155, 527, 1586, 2476, 705, 2478, 4544, 2631, 3025, 2488, 2633, 642, 29, 643, 4885, 898, 897, 641, 31, 4224]

private theorem valid45_02 : ∀ code ∈ codes45_02, validRelationCode code := by
  decide

private theorem cover45_02 : ∀ q : IncreasingFourTail 43 (⟨2, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_02 (increasingFourValues (N := 45) ⟨⟨2, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a02
    (q : IncreasingFourTail 43 (⟨2, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨2, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_02 _ valid45_02 (cover45_02 q)

end MinModulus.SHCFiveCertificate.Generated
