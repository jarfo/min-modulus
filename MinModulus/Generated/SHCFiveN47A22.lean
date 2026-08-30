import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_22 : List ℕ := [1185]

private theorem valid47_22 : ∀ code ∈ codes47_22, validRelationCode code := by
  decide

private theorem cover47_22 : ∀ q : IncreasingFourTail 45 (⟨22, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_22 (increasingFourValues (N := 47) ⟨⟨22, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a22
    (q : IncreasingFourTail 45 (⟨22, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨22, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_22 _ valid47_22 (cover47_22 q)

end MinModulus.SHCFiveCertificate.Generated
