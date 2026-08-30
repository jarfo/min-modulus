import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_15 : List ℕ := [17, 521, 261, 131, 1186, 772, 278, 4265, 4584, 402, 713, 279, 4425, 589, 403, 153, 773, 4884, 642, 4227, 2308, 2626, 85, 2631, 4387, 643, 4232, 2468, 11, 519, 2786, 10, 4234, 321, 518, 2305, 1905, 209, 2624, 2465, 3585, 193, 1187, 1865, 3757, 3745, 6, 1984, 2545, 1988, 19, 3746, 3586, 833, 897, 5036, 1528, 89, 3273, 387, 2958, 1993, 28, 641, 5186, 386, 837, 2546, 3268, 770, 385, 2064, 1907, 3767, 12, 774, 526, 21, 4864, 3105, 5505, 1548, 201, 337, 771, 523, 27, 4547, 1992, 24, 20, 524, 705, 401, 263, 4224, 3025, 3946]

private theorem valid53_15 : ∀ code ∈ codes53_15, validRelationCode code := by
  decide

private theorem cover53_15 : ∀ q : IncreasingFourTail 51 (⟨15, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_15 (increasingFourValues (N := 53) ⟨⟨15, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a15
    (q : IncreasingFourTail 51 (⟨15, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨15, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_15 _ valid53_15 (cover53_15 q)

end MinModulus.SHCFiveCertificate.Generated
