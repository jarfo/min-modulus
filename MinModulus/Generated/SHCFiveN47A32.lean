import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_32 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308]

private theorem valid47_32 : ∀ code ∈ codes47_32, validRelationCode code := by
  decide

private theorem cover47_32 : ∀ q : IncreasingFourTail 45 (⟨32, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_32 (increasingFourValues (N := 47) ⟨⟨32, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a32
    (q : IncreasingFourTail 45 (⟨32, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨32, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_32 _ valid47_32 (cover47_32 q)

end MinModulus.SHCFiveCertificate.Generated
