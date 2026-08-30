import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_04 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 3785, 2485, 402, 642, 2626, 643, 403, 2786, 524, 2306, 20, 85, 589, 2631, 3765, 209, 773, 2468, 153, 401, 2466, 641, 385, 2546, 3746, 4234, 774, 775, 217, 525, 321, 2305, 2628, 4237, 2788, 3185, 4265, 465, 4547, 2633, 3024, 387, 155, 2148, 449, 4225, 3946, 1508, 4884, 526, 4544, 2648, 386, 93, 769, 13]

private theorem valid45_04 : ∀ code ∈ codes45_04, validRelationCode code := by
  decide

private theorem cover45_04 : ∀ q : IncreasingFourTail 43 (⟨4, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_04 (increasingFourValues (N := 45) ⟨⟨4, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a04
    (q : IncreasingFourTail 43 (⟨4, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨4, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_04 _ valid45_04 (cover45_04 q)

end MinModulus.SHCFiveCertificate.Generated
