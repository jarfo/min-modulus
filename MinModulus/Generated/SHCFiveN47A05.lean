import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_05 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 402, 642, 2626, 403, 643, 2786, 85, 589, 2631, 153, 773, 4387, 4232, 2468, 4234, 4884, 1347, 27, 3785, 2485, 209, 2465, 385, 4425, 2546, 3765, 3746, 401, 2466, 3586, 524, 2306, 2944, 4224, 641, 321, 12, 10, 713, 21, 1905, 20, 1186, 525, 387, 3264, 2958, 774, 771, 5191, 770, 837, 4544, 1667, 775, 2305, 89, 77, 897, 1546, 3767, 24, 386, 526, 465, 705, 13]

private theorem valid47_05 : ∀ code ∈ codes47_05, validRelationCode code := by
  decide

private theorem cover47_05 : ∀ q : IncreasingFourTail 45 (⟨5, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_05 (increasingFourValues (N := 47) ⟨⟨5, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a05
    (q : IncreasingFourTail 45 (⟨5, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨5, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_05 _ valid47_05 (cover47_05 q)

end MinModulus.SHCFiveCertificate.Generated
