import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_40 : List ℕ := [17, 402]

private theorem valid47_40 : ∀ code ∈ codes47_40, validRelationCode code := by
  decide

private theorem cover47_40 : ∀ q : IncreasingFourTail 45 (⟨40, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_40 (increasingFourValues (N := 47) ⟨⟨40, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a40
    (q : IncreasingFourTail 45 (⟨40, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨40, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_40 _ valid47_40 (cover47_40 q)

end MinModulus.SHCFiveCertificate.Generated
