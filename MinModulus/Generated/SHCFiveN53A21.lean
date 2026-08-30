import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_21 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 3585, 3745, 4227, 772, 2308, 1865, 2545, 773, 2468, 85, 642, 402, 2626, 153, 643, 2631, 589, 1347, 4232, 2786, 4387, 403, 4884, 209, 321, 5025, 2465, 10, 713, 833, 2305, 518, 1905, 2624, 386, 385, 4425, 1667, 1868, 770, 278, 387, 2476, 519, 22, 465, 89, 771, 279, 4265, 3756, 2706, 1346, 28, 14, 27, 4885]

private theorem valid53_21 : ∀ code ∈ codes53_21, validRelationCode code := by
  decide

private theorem cover53_21 : ∀ q : IncreasingFourTail 51 (⟨21, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_21 (increasingFourValues (N := 53) ⟨⟨21, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a21
    (q : IncreasingFourTail 51 (⟨21, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨21, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_21 _ valid53_21 (cover53_21 q)

end MinModulus.SHCFiveCertificate.Generated
