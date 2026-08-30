import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_14 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 772, 4227, 2308, 402, 642, 2626, 4884, 153, 773, 589, 2631, 85, 1984, 4232, 4387, 2468, 385, 2546, 643, 1507, 5025, 770, 5184, 10, 1548, 465, 278, 518]

private theorem valid39_14 : ∀ code ∈ codes39_14, validRelationCode code := by
  decide

private theorem cover39_14 : ∀ q : IncreasingFourTail 37 (⟨14, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_14 (increasingFourValues (N := 39) ⟨⟨14, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a14
    (q : IncreasingFourTail 37 (⟨14, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨14, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_14 _ valid39_14 (cover39_14 q)

end MinModulus.SHCFiveCertificate.Generated
