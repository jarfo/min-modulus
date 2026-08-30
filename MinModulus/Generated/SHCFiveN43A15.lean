import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_15 : List ℕ := [17, 521, 261, 131, 1186, 772, 4227, 2308, 7, 153, 773, 402, 4232, 2468, 4387, 642, 2626, 2786, 643, 2631, 589, 403, 4884, 85, 4234, 1984, 770, 713, 4870, 1668, 209, 4584, 3757, 1667, 321, 2624, 1905, 518, 2064, 27, 10, 3344, 4425, 386, 278, 22, 833, 385, 2024]

private theorem valid43_15 : ∀ code ∈ codes43_15, validRelationCode code := by
  decide

private theorem cover43_15 : ∀ q : IncreasingFourTail 41 (⟨15, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_15 (increasingFourValues (N := 43) ⟨⟨15, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a15
    (q : IncreasingFourTail 41 (⟨15, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨15, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_15 _ valid43_15 (cover43_15 q)

end MinModulus.SHCFiveCertificate.Generated
