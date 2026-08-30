import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes37_29 : List ℕ := [17, 521, 770]

private theorem valid37_29 : ∀ code ∈ codes37_29, validRelationCode code := by
  decide

private theorem cover37_29 : ∀ q : IncreasingFourTail 35 (⟨29, by norm_num⟩ : Fin 32),
    coveredNat 37 codes37_29 (increasingFourValues (N := 37) ⟨⟨29, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate37_a29
    (q : IncreasingFourTail 35 (⟨29, by norm_num⟩ : Fin 32)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 37 (increasingFourValues (N := 37) ⟨⟨29, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 37 codes37_29 _ valid37_29 (cover37_29 q)

end MinModulus.SHCFiveCertificate.Generated
