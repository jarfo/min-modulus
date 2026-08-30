import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_05 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 3765, 642, 4387, 4232, 402, 2626, 403, 2786, 643, 589, 2631, 773, 2468, 85, 153, 4234, 4884, 27, 209, 2465, 4425, 524, 3746, 2306, 385, 2546, 20, 641, 401, 2944, 321, 1905, 713, 10, 12, 770, 21, 1347, 775, 2305, 2148, 2466, 3586, 1186, 3906, 2788, 89, 525, 5346, 4552, 154, 25, 15, 1546, 28, 386, 769, 13]

private theorem valid45_05 : ∀ code ∈ codes45_05, validRelationCode code := by
  decide

private theorem cover45_05 : ∀ q : IncreasingFourTail 43 (⟨5, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_05 (increasingFourValues (N := 45) ⟨⟨5, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a05
    (q : IncreasingFourTail 43 (⟨5, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨5, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_05 _ valid45_05 (cover45_05 q)

end MinModulus.SHCFiveCertificate.Generated
