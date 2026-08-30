import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_11 : List ℕ := [17, 521, 261, 131, 772, 278, 4265, 402, 4584, 279, 713, 4425, 589, 403, 153, 773, 4884, 642, 2308, 1868, 85, 2631, 643, 2626, 4227, 2786, 2465, 4232, 2468, 1905, 209, 321, 518, 2064, 2624, 1186, 10, 4387, 2305, 4234, 3746, 1993, 770, 18, 385, 27, 3745, 522, 262, 2546, 2648, 386, 20, 193, 201, 577, 3586, 526, 217, 897, 387, 1665]

private theorem valid43_11 : ∀ code ∈ codes43_11, validRelationCode code := by
  decide

private theorem cover43_11 : ∀ q : IncreasingFourTail 41 (⟨11, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_11 (increasingFourValues (N := 43) ⟨⟨11, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a11
    (q : IncreasingFourTail 41 (⟨11, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨11, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_11 _ valid43_11 (cover43_11 q)

end MinModulus.SHCFiveCertificate.Generated
