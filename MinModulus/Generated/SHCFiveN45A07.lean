import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_07 : List ℕ := [17, 521, 261, 131, 2024, 2704, 3904, 201, 337, 577, 18, 522, 262, 19, 523, 2308, 772, 4227, 263, 3765, 4387, 4232, 773, 2468, 153, 209, 713, 321, 642, 402, 1825, 1347, 643, 2626, 1665, 403, 2786, 2631, 85, 589, 1905, 2624, 2465, 13, 385, 833, 4425, 10, 2305, 5025, 12, 1837, 386, 4397, 524, 27, 3785, 837, 770, 20, 11, 1667, 4237, 1187, 14, 4106, 401, 25, 5204, 2633, 641, 2628, 28, 774, 769, 4224, 154, 30, 961, 897, 29]

private theorem valid45_07 : ∀ code ∈ codes45_07, validRelationCode code := by
  decide

private theorem cover45_07 : ∀ q : IncreasingFourTail 43 (⟨7, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_07 (increasingFourValues (N := 45) ⟨⟨7, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a07
    (q : IncreasingFourTail 43 (⟨7, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨7, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_07 _ valid45_07 (cover45_07 q)

end MinModulus.SHCFiveCertificate.Generated
