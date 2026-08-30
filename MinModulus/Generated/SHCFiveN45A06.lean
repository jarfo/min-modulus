import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_06 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 263, 1825, 1665, 772, 4227, 2308, 402, 642, 2626, 3765, 643, 4387, 4232, 85, 403, 2786, 153, 773, 589, 2468, 2631, 321, 4234, 4884, 2064, 26, 2305, 1905, 4265, 209, 713, 518, 2465, 10, 4425, 3586, 2148, 3756, 21, 12, 449, 2624, 401, 525, 385, 11, 3264, 4224, 1507, 524, 1546, 2306, 1187, 93, 1992, 3912, 2788, 774, 89, 23, 5514, 1667, 2808, 20, 154, 526, 217, 4584]

private theorem valid45_06 : ∀ code ∈ codes45_06, validRelationCode code := by
  decide

private theorem cover45_06 : ∀ q : IncreasingFourTail 43 (⟨6, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_06 (increasingFourValues (N := 45) ⟨⟨6, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a06
    (q : IncreasingFourTail 43 (⟨6, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨6, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_06 _ valid45_06 (cover45_06 q)

end MinModulus.SHCFiveCertificate.Generated
