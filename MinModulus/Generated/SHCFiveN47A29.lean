import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_29 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 402, 4227, 2308, 85, 589, 2631, 403, 643, 2786, 386, 93, 4387]

private theorem valid47_29 : ∀ code ∈ codes47_29, validRelationCode code := by
  decide

private theorem cover47_29 : ∀ q : IncreasingFourTail 45 (⟨29, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_29 (increasingFourValues (N := 47) ⟨⟨29, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a29
    (q : IncreasingFourTail 45 (⟨29, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨29, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_29 _ valid47_29 (cover47_29 q)

end MinModulus.SHCFiveCertificate.Generated
