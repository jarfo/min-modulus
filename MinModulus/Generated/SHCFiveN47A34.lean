import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_34 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 85, 77, 386, 770]

private theorem valid47_34 : ∀ code ∈ codes47_34, validRelationCode code := by
  decide

private theorem cover47_34 : ∀ q : IncreasingFourTail 45 (⟨34, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_34 (increasingFourValues (N := 47) ⟨⟨34, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a34
    (q : IncreasingFourTail 45 (⟨34, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨34, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_34 _ valid47_34 (cover47_34 q)

end MinModulus.SHCFiveCertificate.Generated
