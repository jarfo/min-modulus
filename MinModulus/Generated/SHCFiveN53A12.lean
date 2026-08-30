import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_12 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 773, 403, 643, 4387, 2786, 2631, 2468, 4884, 4234, 1507, 2704, 2024, 3904, 4265, 321, 11, 2305, 201, 1825, 209, 518, 713, 2624, 1905, 4425, 10, 2465, 337, 2064, 577, 4584, 3765, 278, 522, 262, 1665, 3746, 1988, 18, 3586, 519, 2148, 26, 3906, 4066, 401, 387, 12, 89, 2944, 1527, 3907, 1668, 386, 770, 193, 385, 2958, 3273, 774, 5036, 5191, 771, 1865, 3585, 3912, 524, 2954, 217, 899, 775, 3756, 1868, 3268, 14, 4224, 5025, 2466, 4866, 4876, 28, 154, 961, 449, 641, 3024]

private theorem valid53_12 : ∀ code ∈ codes53_12, validRelationCode code := by
  decide

private theorem cover53_12 : ∀ q : IncreasingFourTail 51 (⟨12, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_12 (increasingFourValues (N := 53) ⟨⟨12, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a12
    (q : IncreasingFourTail 51 (⟨12, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨12, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_12 _ valid53_12 (cover53_12 q)

end MinModulus.SHCFiveCertificate.Generated
