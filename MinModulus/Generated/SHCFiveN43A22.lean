import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_22 : List ℕ := [17, 521, 261, 131, 3785, 2485, 4227, 642, 772, 402, 2626, 2308, 85, 643, 4234, 773, 4544, 2468, 705, 23, 153, 4232, 403, 2786, 4387, 589, 898, 833, 899, 387]

private theorem valid43_22 : ∀ code ∈ codes43_22, validRelationCode code := by
  decide

private theorem cover43_22 : ∀ q : IncreasingFourTail 41 (⟨22, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_22 (increasingFourValues (N := 43) ⟨⟨22, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a22
    (q : IncreasingFourTail 41 (⟨22, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨22, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_22 _ valid43_22 (cover43_22 q)

end MinModulus.SHCFiveCertificate.Generated
