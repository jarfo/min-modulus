import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_39 : List ℕ := [17, 521, 770]

private theorem valid47_39 : ∀ code ∈ codes47_39, validRelationCode code := by
  decide

private theorem cover47_39 : ∀ q : IncreasingFourTail 45 (⟨39, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_39 (increasingFourValues (N := 47) ⟨⟨39, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a39
    (q : IncreasingFourTail 45 (⟨39, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨39, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_39 _ valid47_39 (cover47_39 q)

end MinModulus.SHCFiveCertificate.Generated
