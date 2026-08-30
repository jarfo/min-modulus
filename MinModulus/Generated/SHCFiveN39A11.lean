import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_11 : List ℕ := [17, 521, 261, 131, 1186, 772, 278, 4584, 402, 713, 589, 403, 279, 4884, 153, 773, 2546, 4227, 10, 2308, 642, 2626, 518, 85, 2631, 4387, 643, 4232, 2468, 321, 519, 209, 2786, 11, 2624, 27, 4234, 18, 19, 193, 1993, 1546, 1827, 386, 262]

private theorem valid39_11 : ∀ code ∈ codes39_11, validRelationCode code := by
  decide

private theorem cover39_11 : ∀ q : IncreasingFourTail 37 (⟨11, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_11 (increasingFourValues (N := 39) ⟨⟨11, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a11
    (q : IncreasingFourTail 37 (⟨11, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨11, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_11 _ valid39_11 (cover39_11 q)

end MinModulus.SHCFiveCertificate.Generated
