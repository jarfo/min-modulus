import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_16 : List ℕ := [17, 521, 261, 131, 1186, 7, 772, 402, 4227, 2308, 642, 2626, 153, 773, 4884, 4232, 589, 2468, 4387, 2631, 643, 85, 2786, 403, 1507, 4234, 1548, 4870, 385, 1837, 321, 1984, 833, 2624, 10, 2305, 1827, 12, 22, 6, 11, 2546, 278, 518, 465, 2465, 713, 77, 526, 705, 897, 527]

private theorem valid45_16 : ∀ code ∈ codes45_16, validRelationCode code := by
  decide

private theorem cover45_16 : ∀ q : IncreasingFourTail 43 (⟨16, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_16 (increasingFourValues (N := 45) ⟨⟨16, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a16
    (q : IncreasingFourTail 43 (⟨16, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨16, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_16 _ valid45_16 (cover45_16 q)

end MinModulus.SHCFiveCertificate.Generated
