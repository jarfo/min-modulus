import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_10 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 11, 279, 519, 85, 589, 2631, 4265, 2305, 403, 2786, 153, 773, 278, 2468, 10, 643, 4232, 4387, 518, 321, 4425, 713, 1905, 209, 2465, 1186, 4584, 1187, 2624, 1825, 2064, 3904, 4234, 337, 770, 263, 2808, 3907, 387, 1827, 522, 262, 201, 577, 775, 18, 89, 897, 2944, 1667, 386, 193, 217, 93, 769, 19, 523]

private theorem valid43_10 : ∀ code ∈ codes43_10, validRelationCode code := by
  decide

private theorem cover43_10 : ∀ q : IncreasingFourTail 41 (⟨10, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_10 (increasingFourValues (N := 43) ⟨⟨10, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a10
    (q : IncreasingFourTail 41 (⟨10, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨10, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_10 _ valid43_10 (cover43_10 q)

end MinModulus.SHCFiveCertificate.Generated
