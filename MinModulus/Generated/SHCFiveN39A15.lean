import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_15 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 772, 4227, 2308, 3585, 3745, 773, 2468, 4884, 4387, 2626, 642, 153, 4232, 402, 2631, 1667, 1668, 518, 278, 705, 2706, 22, 209, 321, 386, 770, 449, 89]

private theorem valid39_15 : ∀ code ∈ codes39_15, validRelationCode code := by
  decide

private theorem cover39_15 : ∀ q : IncreasingFourTail 37 (⟨15, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_15 (increasingFourValues (N := 39) ⟨⟨15, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a15
    (q : IncreasingFourTail 37 (⟨15, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨15, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_15 _ valid39_15 (cover39_15 q)

end MinModulus.SHCFiveCertificate.Generated
