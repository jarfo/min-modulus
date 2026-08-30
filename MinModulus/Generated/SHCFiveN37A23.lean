import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_23 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 403, 589, 2706]

private theorem valid37_23 : ∀ code ∈ codes37_23, validRelationCode code := by
  decide

private theorem cover37_23 : ∀ q : IncreasingFourTail 35 (⟨23, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_23 (increasingFourValues (N := 37) ⟨⟨23, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a23
    (q : IncreasingFourTail 35 (⟨23, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨23, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_23 _ valid37_23 (cover37_23 q)

end MinModulus.SHCFiveCertificate.Generated
