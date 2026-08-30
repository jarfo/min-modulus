import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_25 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 589, 403, 4387, 4227, 4232, 2786, 2631, 2308, 85, 153, 773, 643, 386, 2485, 1347, 1667, 770, 3907, 387]

private theorem valid47_25 : ∀ code ∈ codes47_25, validRelationCode code := by
  decide

private theorem cover47_25 : ∀ q : IncreasingFourTail 45 (⟨25, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_25 (increasingFourValues (N := 47) ⟨⟨25, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a25
    (q : IncreasingFourTail 45 (⟨25, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨25, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_25 _ valid47_25 (cover47_25 q)

end MinModulus.SHCFiveCertificate.Generated
