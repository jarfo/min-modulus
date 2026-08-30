import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_03 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 3785, 2485, 4227, 772, 2308, 524, 2306, 20, 643, 403, 2786, 642, 402, 2626, 775, 2788, 4707, 155, 589, 85, 2631, 21, 4385, 3765, 4106, 4544, 385, 4225, 2546, 3746, 23, 527, 401, 641, 386, 3025, 3344, 774, 3185, 526, 465, 4884, 2148, 4224, 2628, 22, 387, 3024, 2706, 705, 3105, 2466, 525, 1186, 3756, 3927, 217, 153, 5824, 5505, 2945, 4865]

private theorem valid45_03 : ∀ code ∈ codes45_03, validRelationCode code := by
  decide

private theorem cover45_03 : ∀ q : IncreasingFourTail 43 (⟨3, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_03 (increasingFourValues (N := 45) ⟨⟨3, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a03
    (q : IncreasingFourTail 43 (⟨3, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨3, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_03 _ valid45_03 (cover45_03 q)

end MinModulus.SHCFiveCertificate.Generated
