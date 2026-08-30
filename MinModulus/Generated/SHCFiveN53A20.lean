import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes53_20 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 772, 4227, 2308, 402, 642, 2626, 3585, 773, 2468, 589, 2631, 85, 153, 4232, 4387, 643, 4884, 2786, 403, 1865, 2545, 3745, 209, 713, 4425, 518, 321, 1905, 2465, 4584, 278, 4265, 10, 2305, 2624, 465, 1827, 1828, 1868, 705, 11, 519, 4234, 833, 4870, 385, 1507, 1587, 3767, 12, 13, 771, 3273, 26, 899, 387, 3344, 5510]

private theorem valid53_20 : ∀ code ∈ codes53_20, validRelationCode code := by
  decide

private theorem cover53_20 : ∀ q : IncreasingFourTail 51 (⟨20, by norm_num⟩ : Fin 48),
    coveredNat 53 codes53_20 (increasingFourValues (N := 53) ⟨⟨20, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate53_a20
    (q : IncreasingFourTail 51 (⟨20, by norm_num⟩ : Fin 48)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 53 (increasingFourValues (N := 53) ⟨⟨20, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 53 codes53_20 _ valid53_20 (cover53_20 q)

end MinModulus.SHCFiveCertificate.Generated
