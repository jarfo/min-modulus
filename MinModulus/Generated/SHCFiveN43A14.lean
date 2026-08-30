import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_14 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 4584, 4425, 4265, 278, 279, 589, 403, 153, 773, 4884, 1868, 2546, 4227, 2626, 4232, 2308, 4387, 85, 10, 11, 519, 2305, 2631, 1507, 642, 518, 2624, 1905, 2465, 2468, 209, 643, 321, 5184, 1827, 6, 2786, 4876, 1187, 26, 12, 193, 385]

private theorem valid43_14 : ∀ code ∈ codes43_14, validRelationCode code := by
  decide

private theorem cover43_14 : ∀ q : IncreasingFourTail 41 (⟨14, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_14 (increasingFourValues (N := 43) ⟨⟨14, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a14
    (q : IncreasingFourTail 41 (⟨14, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨14, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_14 _ valid43_14 (cover43_14 q)

end MinModulus.SHCFiveCertificate.Generated
