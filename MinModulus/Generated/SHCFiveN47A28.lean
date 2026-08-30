import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_28 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 386, 403, 643, 773, 4387, 770, 2954, 3907]

private theorem valid47_28 : ∀ code ∈ codes47_28, validRelationCode code := by
  decide

private theorem cover47_28 : ∀ q : IncreasingFourTail 45 (⟨28, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_28 (increasingFourValues (N := 47) ⟨⟨28, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a28
    (q : IncreasingFourTail 45 (⟨28, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨28, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_28 _ valid47_28 (cover47_28 q)

end MinModulus.SHCFiveCertificate.Generated
