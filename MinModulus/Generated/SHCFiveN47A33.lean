import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_33 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 403, 589, 2706]

private theorem valid47_33 : ∀ code ∈ codes47_33, validRelationCode code := by
  decide

private theorem cover47_33 : ∀ q : IncreasingFourTail 45 (⟨33, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_33 (increasingFourValues (N := 47) ⟨⟨33, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a33
    (q : IncreasingFourTail 45 (⟨33, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨33, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_33 _ valid47_33 (cover47_33 q)

end MinModulus.SHCFiveCertificate.Generated
