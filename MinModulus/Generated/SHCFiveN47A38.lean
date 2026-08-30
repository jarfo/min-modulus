import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_38 : List ℕ := [17, 521, 261, 772]

private theorem valid47_38 : ∀ code ∈ codes47_38, validRelationCode code := by
  decide

private theorem cover47_38 : ∀ q : IncreasingFourTail 45 (⟨38, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_38 (increasingFourValues (N := 47) ⟨⟨38, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a38
    (q : IncreasingFourTail 45 (⟨38, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨38, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_38 _ valid47_38 (cover47_38 q)

end MinModulus.SHCFiveCertificate.Generated
