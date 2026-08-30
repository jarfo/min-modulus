import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_14 : List ℕ := [17, 521, 261, 131, 1186, 7, 6, 193, 1984, 772, 4227, 2308, 153, 773, 4387, 4232, 2468, 4884, 2626, 402, 642, 3745, 10, 278, 518, 5184, 4876, 321, 643, 1827, 833]

private theorem valid37_14 : ∀ code ∈ codes37_14, validRelationCode code := by
  decide

private theorem cover37_14 : ∀ q : IncreasingFourTail 35 (⟨14, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_14 (increasingFourValues (N := 37) ⟨⟨14, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a14
    (q : IncreasingFourTail 35 (⟨14, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨14, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_14 _ valid37_14 (cover37_14 q)

end MinModulus.SHCFiveCertificate.Generated
