import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_17 : List ℕ := [17, 521, 261, 131, 1186, 772, 4584, 4265, 278, 402, 713, 4425, 279, 589, 403, 153, 773, 4884, 4227, 2308, 2064, 2624, 2626, 642, 85, 2631, 4387, 209, 643, 4232, 2468, 2465, 321, 2786, 1905, 2305, 4234, 518, 1825, 10, 519, 1984, 1665, 18, 262, 577, 3904, 201, 337, 263, 2546, 522, 4870, 19, 523, 3586, 193, 3185, 385, 1586, 4106, 1837, 3907, 12, 465, 2024, 2306, 1827, 705, 387, 4385, 1527, 20, 524, 897, 771, 31, 2944, 5025]

private theorem valid53_17 : ∀ code ∈ codes53_17, validRelationCode code := by
  decide

private theorem cover53_17 : ∀ q : IncreasingFourTail 51 (⟨17, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_17 (increasingFourValues (N := 53) ⟨⟨17, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a17
    (q : IncreasingFourTail 51 (⟨17, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨17, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_17 _ valid53_17 (cover53_17 q)

end MinModulus.SHCFiveCertificate.Generated
