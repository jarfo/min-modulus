import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_12 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 278, 279, 4425, 4584, 153, 773, 589, 403, 4884, 4227, 642, 2626, 2308, 85, 2631, 4387, 643, 4232, 2468, 10, 2786, 518, 11, 519, 321, 4234, 1905, 18, 2624, 19, 1527, 193, 209, 263, 5504, 1865, 3745, 1984, 1528, 770, 6, 2545, 4876, 1187, 26, 775, 12, 28, 837, 7]

private theorem valid43_12 : ∀ code ∈ codes43_12, validRelationCode code := by
  decide

private theorem cover43_12 : ∀ q : IncreasingFourTail 41 (⟨12, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_12 (increasingFourValues (N := 43) ⟨⟨12, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a12
    (q : IncreasingFourTail 41 (⟨12, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨12, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_12 _ valid43_12 (cover43_12 q)

end MinModulus.SHCFiveCertificate.Generated
