import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_37 : List ℕ := [17, 521, 261, 131, 772]

private theorem valid47_37 : ∀ code ∈ codes47_37, validRelationCode code := by
  decide

private theorem cover47_37 : ∀ q : IncreasingFourTail 45 (⟨37, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_37 (increasingFourValues (N := 47) ⟨⟨37, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a37
    (q : IncreasingFourTail 45 (⟨37, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨37, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_37 _ valid47_37 (cover47_37 q)

end MinModulus.SHCFiveCertificate.Generated
