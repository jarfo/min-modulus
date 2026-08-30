import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_13 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 772, 4227, 2308, 153, 773, 402, 4387, 4232, 642, 2468, 2626, 589, 2631, 85, 2786, 643, 2546, 1984, 5025, 833, 385, 4884, 10, 193, 28, 386, 26]

private theorem valid37_13 : ∀ code ∈ codes37_13, validRelationCode code := by
  decide

private theorem cover37_13 : ∀ q : IncreasingFourTail 35 (⟨13, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_13 (increasingFourValues (N := 37) ⟨⟨13, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a13
    (q : IncreasingFourTail 35 (⟨13, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨13, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_13 _ valid37_13 (cover37_13 q)

end MinModulus.SHCFiveCertificate.Generated
