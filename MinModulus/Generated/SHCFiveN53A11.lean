import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_11 : List ℕ := [17, 521, 261, 131, 2024, 2704, 4227, 3904, 772, 2308, 402, 642, 2626, 403, 643, 2786, 85, 589, 2631, 1825, 153, 773, 201, 577, 337, 4387, 4232, 2468, 4234, 4884, 262, 1665, 522, 18, 209, 4425, 263, 713, 321, 523, 1186, 1905, 4265, 2465, 10, 2624, 518, 19, 2305, 4584, 278, 1187, 519, 2064, 385, 1347, 770, 387, 12, 11, 3906, 386, 27, 4865, 3907, 2954, 4066, 3586, 1668, 771, 1527, 2648, 20, 89, 2546, 4087, 2808, 2866, 1667, 2958, 2706, 28, 154, 217, 4385, 5186, 641, 15, 5824, 3745, 3585, 1987, 24, 526, 30, 961, 193, 833, 897, 769, 155, 5514]

private theorem valid53_11 : ∀ code ∈ codes53_11, validRelationCode code := by
  decide

private theorem cover53_11 : ∀ q : IncreasingFourTail 51 (⟨11, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_11 (increasingFourValues (N := 53) ⟨⟨11, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a11
    (q : IncreasingFourTail 51 (⟨11, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨11, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_11 _ valid53_11 (cover53_11 q)

end MinModulus.SHCFiveCertificate.Generated
