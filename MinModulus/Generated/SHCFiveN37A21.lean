import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_21 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 85, 153, 773, 643, 402, 4227, 386, 770, 1667]

private theorem valid37_21 : ∀ code ∈ codes37_21, validRelationCode code := by
  decide

private theorem cover37_21 : ∀ q : IncreasingFourTail 35 (⟨21, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_21 (increasingFourValues (N := 37) ⟨⟨21, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a21
    (q : IncreasingFourTail 35 (⟨21, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨21, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_21 _ valid37_21 (cover37_21 q)

end MinModulus.SHCFiveCertificate.Generated
