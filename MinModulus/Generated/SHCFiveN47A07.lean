import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_07 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 772, 4227, 2308, 1825, 1665, 3765, 4387, 4232, 642, 773, 2468, 153, 402, 2626, 643, 2786, 2631, 589, 403, 1347, 85, 209, 321, 713, 1905, 2465, 4425, 2624, 2485, 3785, 4870, 833, 2305, 10, 385, 524, 13, 5025, 20, 770, 386, 1837, 12, 401, 641, 3264, 1187, 27, 2954, 4397, 4237, 154, 837, 11, 4884, 769, 525, 5204, 4865, 4224, 5514, 3907, 2628, 898, 93, 4385, 4265, 3912, 774, 21]

private theorem valid47_07 : ∀ code ∈ codes47_07, validRelationCode code := by
  decide

private theorem cover47_07 : ∀ q : IncreasingFourTail 45 (⟨7, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_07 (increasingFourValues (N := 47) ⟨⟨7, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a07
    (q : IncreasingFourTail 45 (⟨7, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨7, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_07 _ valid47_07 (cover47_07 q)

end MinModulus.SHCFiveCertificate.Generated
