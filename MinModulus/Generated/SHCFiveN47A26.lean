import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_26 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 153, 4232, 773, 403, 643, 4387, 2786, 2631, 2468, 89, 2485, 2866, 898, 386]

private theorem valid47_26 : ∀ code ∈ codes47_26, validRelationCode code := by
  decide

private theorem cover47_26 : ∀ q : IncreasingFourTail 45 (⟨26, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_26 (increasingFourValues (N := 47) ⟨⟨26, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a26
    (q : IncreasingFourTail 45 (⟨26, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨26, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_26 _ valid47_26 (cover47_26 q)

end MinModulus.SHCFiveCertificate.Generated
