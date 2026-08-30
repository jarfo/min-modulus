import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_13 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 1347, 402, 4227, 2308, 10, 2305, 278, 518, 4265, 2624, 11, 321, 2465, 2631, 2786, 1187, 85, 643, 4425, 773, 153, 209, 713, 1905, 2468, 4232, 589, 4387, 403, 519, 279, 4584, 4884, 2064, 4234, 1186, 770, 1546, 3746, 12, 833, 1825, 522, 385, 3586, 3907, 1528, 2546, 18, 386, 262, 193, 201, 3264, 3757, 387, 1865, 3585, 3906, 401, 263, 1837, 14, 89, 2944, 1827, 577, 775, 774, 6, 897, 769, 525, 771, 523, 5036, 217, 337, 2866, 1992, 3273, 898, 526, 25, 31, 2466, 4547, 24, 20, 22, 30, 837, 21, 19, 27, 5184, 2954]

private theorem valid53_13 : ∀ code ∈ codes53_13, validRelationCode code := by
  decide

private theorem cover53_13 : ∀ q : IncreasingFourTail 51 (⟨13, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_13 (increasingFourValues (N := 53) ⟨⟨13, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a13
    (q : IncreasingFourTail 51 (⟨13, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨13, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_13 _ valid53_13 (cover53_13 q)

end MinModulus.SHCFiveCertificate.Generated
