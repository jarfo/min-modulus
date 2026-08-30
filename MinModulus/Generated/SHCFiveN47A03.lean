import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_03 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 1187, 1347, 2626, 642, 402, 524, 2306, 20, 2786, 2466, 403, 643, 401, 774, 153, 21, 85, 641, 4225, 525, 154, 773, 3765, 770, 4224, 2628, 385, 1837, 5186, 2148, 386, 2706, 3746, 22, 526, 589, 3344, 465, 3025, 449, 2954, 5510, 2788, 4865, 3024, 4387, 93, 775, 769, 3756, 1827, 837, 4884, 3105, 12, 387, 5504, 5514, 4385, 1186, 1907, 4237, 26]

private theorem valid47_03 : ∀ code ∈ codes47_03, validRelationCode code := by
  decide

private theorem cover47_03 : ∀ q : IncreasingFourTail 45 (⟨3, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_03 (increasingFourValues (N := 47) ⟨⟨3, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a03
    (q : IncreasingFourTail 45 (⟨3, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨3, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_03 _ valid47_03 (cover47_03 q)

end MinModulus.SHCFiveCertificate.Generated
