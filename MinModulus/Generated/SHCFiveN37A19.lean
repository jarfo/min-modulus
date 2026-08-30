import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_19 : List ℕ := [17, 521, 261, 131, 3785, 2485, 4227, 772, 2308, 153, 402, 773, 4232, 642, 2786, 4387, 2631, 2626, 77, 2808]

private theorem valid37_19 : ∀ code ∈ codes37_19, validRelationCode code := by
  decide

private theorem cover37_19 : ∀ q : IncreasingFourTail 35 (⟨19, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_19 (increasingFourValues (N := 37) ⟨⟨19, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a19
    (q : IncreasingFourTail 35 (⟨19, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨19, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_19 _ valid37_19 (cover37_19 q)

end MinModulus.SHCFiveCertificate.Generated
