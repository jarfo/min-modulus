import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_14 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 278, 4584, 279, 589, 403, 153, 773, 4884, 518, 321, 2308, 642, 2626, 209, 2631, 4227, 2786, 643, 2468, 4232, 4387, 10, 85, 2624, 519, 4234, 2064, 193, 11, 18, 262, 1984, 263, 1527, 522, 19, 5184, 6, 1187, 201, 523, 26, 387, 4876, 385, 13, 4106, 2546, 2306, 20, 524, 1586, 3586, 22, 14, 577, 899]

private theorem valid47_14 : ∀ code ∈ codes47_14, validRelationCode code := by
  decide

private theorem cover47_14 : ∀ q : IncreasingFourTail 45 (⟨14, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_14 (increasingFourValues (N := 47) ⟨⟨14, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a14
    (q : IncreasingFourTail 45 (⟨14, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨14, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_14 _ valid47_14 (cover47_14 q)

end MinModulus.SHCFiveCertificate.Generated
