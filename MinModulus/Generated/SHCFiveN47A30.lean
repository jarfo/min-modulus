import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_30 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 77, 2631, 3911, 153, 773]

private theorem valid47_30 : ∀ code ∈ codes47_30, validRelationCode code := by
  decide

private theorem cover47_30 : ∀ q : IncreasingFourTail 45 (⟨30, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_30 (increasingFourValues (N := 47) ⟨⟨30, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a30
    (q : IncreasingFourTail 45 (⟨30, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨30, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_30 _ valid47_30 (cover47_30 q)

end MinModulus.SHCFiveCertificate.Generated
