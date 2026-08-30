import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_27 : List ℕ := [17, 521, 261, 131, 772]

private theorem valid37_27 : ∀ code ∈ codes37_27, validRelationCode code := by
  decide

private theorem cover37_27 : ∀ q : IncreasingFourTail 35 (⟨27, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_27 (increasingFourValues (N := 37) ⟨⟨27, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a27
    (q : IncreasingFourTail 35 (⟨27, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨27, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_27 _ valid37_27 (cover37_27 q)

end MinModulus.SHCFiveCertificate.Generated
