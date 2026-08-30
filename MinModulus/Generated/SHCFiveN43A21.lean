import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_21 : List ℕ := [17, 521, 261, 131, 3785, 2485, 642, 589, 2468, 772, 2626, 4232, 773, 4884, 2476, 2631, 4387, 4227, 402, 465, 85, 643, 1347, 77, 2954]

private theorem valid43_21 : ∀ code ∈ codes43_21, validRelationCode code := by
  decide

private theorem cover43_21 : ∀ q : IncreasingFourTail 41 (⟨21, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_21 (increasingFourValues (N := 43) ⟨⟨21, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a21
    (q : IncreasingFourTail 41 (⟨21, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨21, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_21 _ valid43_21 (cover43_21 q)

end MinModulus.SHCFiveCertificate.Generated
