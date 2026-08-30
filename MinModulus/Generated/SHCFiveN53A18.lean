import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_18 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 4584, 4425, 4265, 278, 279, 589, 403, 153, 773, 4884, 4227, 2308, 2626, 642, 4232, 2468, 4387, 10, 518, 321, 643, 209, 1905, 2786, 2305, 2465, 2631, 85, 519, 11, 1984, 193, 2624, 1546, 1825, 5025, 4234, 1527, 387, 2064, 1827, 3906, 1828, 12, 262, 465, 201, 385, 3586, 1665, 4885, 3757, 1868, 3745, 3746, 1837, 3273, 770, 705, 3585, 1988, 522, 30, 577, 263, 5186]

private theorem valid53_18 : ∀ code ∈ codes53_18, validRelationCode code := by
  decide

private theorem cover53_18 : ∀ q : IncreasingFourTail 51 (⟨18, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_18 (increasingFourValues (N := 53) ⟨⟨18, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a18
    (q : IncreasingFourTail 51 (⟨18, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨18, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_18 _ valid53_18 (cover53_18 q)

end MinModulus.SHCFiveCertificate.Generated
