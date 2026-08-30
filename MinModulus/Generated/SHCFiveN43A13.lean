import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_13 : List ℕ := [17, 521, 261, 131, 1186, 772, 4584, 278, 402, 713, 589, 403, 279, 4884, 153, 773, 321, 4227, 2626, 642, 2624, 518, 209, 643, 2631, 2308, 4387, 2468, 85, 4232, 2786, 10, 193, 2064, 519, 4234, 1546, 1984, 3767, 1527, 6, 833, 262, 201, 577, 19, 18, 217, 337, 897, 527, 12, 522, 22]

private theorem valid43_13 : ∀ code ∈ codes43_13, validRelationCode code := by
  decide

private theorem cover43_13 : ∀ q : IncreasingFourTail 41 (⟨13, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_13 (increasingFourValues (N := 43) ⟨⟨13, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a13
    (q : IncreasingFourTail 41 (⟨13, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨13, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_13 _ valid43_13 (cover43_13 q)

end MinModulus.SHCFiveCertificate.Generated
