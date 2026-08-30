import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_12 : List ℕ := [17, 521, 261, 131, 1186, 772, 402, 713, 4584, 4265, 278, 279, 589, 403, 153, 773, 4884, 1868, 2546, 4227, 2626, 2308, 4232, 2786, 642, 2468, 209, 643, 2631, 321, 2624, 4387, 85, 2064, 2305, 26, 1187, 10, 518, 22, 577, 3428, 1528, 337]

private theorem valid39_12 : ∀ code ∈ codes39_12, validRelationCode code := by
  decide

private theorem cover39_12 : ∀ q : IncreasingFourTail 37 (⟨12, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_12 (increasingFourValues (N := 39) ⟨⟨12, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a12
    (q : IncreasingFourTail 37 (⟨12, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨12, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_12 _ valid39_12 (cover39_12 q)

end MinModulus.SHCFiveCertificate.Generated
