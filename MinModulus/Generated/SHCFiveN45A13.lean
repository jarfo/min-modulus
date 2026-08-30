import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes45_13 : List ℕ := [17, 521, 261, 131, 1186, 772, 278, 4584, 402, 713, 589, 403, 279, 153, 773, 4884, 10, 642, 518, 4227, 2308, 2626, 85, 643, 2631, 4387, 4232, 2786, 2468, 321, 519, 209, 4234, 11, 2624, 18, 193, 1527, 263, 262, 19, 1984, 1187, 1528, 833, 6, 523, 1837, 89, 385, 387, 27, 2306, 705, 2064, 5204, 12, 386, 770, 22, 201, 837]

private theorem valid45_13 : ∀ code ∈ codes45_13, validRelationCode code := by
  decide

private theorem cover45_13 : ∀ q : IncreasingFourTail 43 (⟨13, by norm_num⟩ : Fin 40),
    coveredNat 45 codes45_13 (increasingFourValues (N := 45) ⟨⟨13, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate45_a13
    (q : IncreasingFourTail 43 (⟨13, by norm_num⟩ : Fin 40)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 45 (increasingFourValues (N := 45) ⟨⟨13, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 45 codes45_13 _ valid45_13 (cover45_13 q)

end MinModulus.SHCFiveCertificate.Generated
