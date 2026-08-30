import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes47_23 : List ℕ := [17, 521, 261, 131, 3785, 2485, 642, 589, 2468, 772, 773, 4884, 2476, 2626, 2631, 85, 643, 4227, 402, 465, 153, 4885, 77, 3756, 1667, 386, 89, 3911, 1347, 4232, 705]

private theorem valid47_23 : ∀ code ∈ codes47_23, validRelationCode code := by
  decide

private theorem cover47_23 : ∀ q : IncreasingFourTail 45 (⟨23, by norm_num⟩ : Fin 42),
    coveredNat 47 codes47_23 (increasingFourValues (N := 47) ⟨⟨23, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate47_a23
    (q : IncreasingFourTail 45 (⟨23, by norm_num⟩ : Fin 42)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 47 (increasingFourValues (N := 47) ⟨⟨23, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 47 codes47_23 _ valid47_23 (cover47_23 q)

end MinModulus.SHCFiveCertificate.Generated
