import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_14 : List ℕ := [17, 521, 261, 131, 772, 402, 279, 278, 713, 4425, 4265, 4584, 589, 403, 153, 773, 4884, 2626, 4227, 642, 2308, 1186, 85, 2631, 4387, 643, 4232, 2468, 2786, 321, 518, 209, 10, 2624, 1905, 2305, 2465, 2064, 4234, 519, 1507, 11, 1187, 1993, 89, 193, 19, 5184, 1865, 523, 3745, 18, 13, 26, 3585, 3757, 5025, 1984, 833, 386, 770, 522, 1527, 3927, 385, 2648, 898, 387, 4876, 2148, 337, 5505, 4885, 3586, 1528, 12, 6, 897, 1825, 771, 1665, 154, 217, 769, 1548, 524, 28, 262, 577, 837, 641, 29, 27, 5514, 4385, 20, 14, 201, 401, 899, 155, 2466]

private theorem valid53_14 : ∀ code ∈ codes53_14, validRelationCode code := by
  decide

private theorem cover53_14 : ∀ q : IncreasingFourTail 51 (⟨14, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_14 (increasingFourValues (N := 53) ⟨⟨14, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a14
    (q : IncreasingFourTail 51 (⟨14, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨14, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_14 _ valid53_14 (cover53_14 q)

end MinModulus.SHCFiveCertificate.Generated
