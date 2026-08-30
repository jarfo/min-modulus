import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_11 : List ℕ := [17, 521, 261, 131, 1186, 772, 4584, 278, 402, 713, 589, 403, 279, 153, 773, 4884, 1868, 2546, 4227, 321, 2626, 4232, 2786, 642, 2468, 209, 643, 4387, 2308, 2631, 85, 2624, 27, 1187, 10, 518, 193, 201, 577, 2064, 526, 337]

private theorem valid37_11 : ∀ code ∈ codes37_11, validRelationCode code := by
  decide

private theorem cover37_11 : ∀ q : IncreasingFourTail 35 (⟨11, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_11 (increasingFourValues (N := 37) ⟨⟨11, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a11
    (q : IncreasingFourTail 35 (⟨11, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨11, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_11 _ valid37_11 (cover37_11 q)

end MinModulus.SHCFiveCertificate.Generated
