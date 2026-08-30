import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_24 : List ℕ := [17, 521, 261, 131, 3785, 2485, 4227, 642, 772, 402, 2626, 2308, 85, 643, 4234, 403, 2786, 153, 773, 589, 2468, 2631, 4232, 4387, 4884, 3756, 1507, 1827, 770, 705, 899, 387]

private theorem valid47_24 : ∀ code ∈ codes47_24, validRelationCode code := by
  decide

private theorem cover47_24 : ∀ q : IncreasingFourTail 45 (⟨24, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_24 (increasingFourValues (N := 47) ⟨⟨24, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a24
    (q : IncreasingFourTail 45 (⟨24, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨24, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_24 _ valid47_24 (cover47_24 q)

end MinModulus.SHCFiveCertificate.Generated
