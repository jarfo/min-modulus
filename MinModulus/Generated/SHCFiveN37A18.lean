import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_18 : List ℕ := [17, 521, 261, 131, 3785, 2485, 642, 4227, 589, 773, 2631, 2468, 772, 402, 465, 4884, 1868, 153, 2808]

private theorem valid37_18 : ∀ code ∈ codes37_18, validRelationCode code := by
  decide

private theorem cover37_18 : ∀ q : IncreasingFourTail 35 (⟨18, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_18 (increasingFourValues (N := 37) ⟨⟨18, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a18
    (q : IncreasingFourTail 35 (⟨18, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨18, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_18 _ valid37_18 (cover37_18 q)

end MinModulus.SHCFiveCertificate.Generated
