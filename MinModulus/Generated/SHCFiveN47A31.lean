import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_31 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 85, 153, 773, 643, 402, 4227, 386, 770, 1667]

private theorem valid47_31 : ∀ code ∈ codes47_31, validRelationCode code := by
  decide

private theorem cover47_31 : ∀ q : IncreasingFourTail 45 (⟨31, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_31 (increasingFourValues (N := 47) ⟨⟨31, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a31
    (q : IncreasingFourTail 45 (⟨31, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨31, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_31 _ valid47_31 (cover47_31 q)

end MinModulus.SHCFiveCertificate.Generated
