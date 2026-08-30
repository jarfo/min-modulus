import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_35 : List ℕ := [17, 521, 261, 131, 772, 642, 2626]

private theorem valid47_35 : ∀ code ∈ codes47_35, validRelationCode code := by
  decide

private theorem cover47_35 : ∀ q : IncreasingFourTail 45 (⟨35, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_35 (increasingFourValues (N := 47) ⟨⟨35, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a35
    (q : IncreasingFourTail 45 (⟨35, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨35, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_35 _ valid47_35 (cover47_35 q)

end MinModulus.SHCFiveCertificate.Generated
