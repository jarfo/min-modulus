import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_16 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 278, 4584, 279, 589, 403, 153, 773, 4884, 518, 321, 2308, 642, 2626, 209, 4227, 2631, 2786, 643, 2468, 4232, 10, 4387, 85, 2624, 519, 4234, 2064, 11, 193, 262, 18, 1984, 19, 522, 263, 6, 1546, 2148, 523, 833, 577, 201, 3586, 13, 387, 1868, 1827, 3757, 12, 26, 385, 5184, 20, 386, 898, 770, 21, 1993, 641, 2546, 1667, 705, 337, 775, 524, 154, 22, 89, 401, 155, 4544, 2944, 3946, 774, 526, 837, 525, 5504, 4876]

private theorem valid53_16 : ∀ code ∈ codes53_16, validRelationCode code := by
  decide

private theorem cover53_16 : ∀ q : IncreasingFourTail 51 (⟨16, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_16 (increasingFourValues (N := 53) ⟨⟨16, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a16
    (q : IncreasingFourTail 51 (⟨16, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨16, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_16 _ valid53_16 (cover53_16 q)

end MinModulus.SHCFiveCertificate.Generated
