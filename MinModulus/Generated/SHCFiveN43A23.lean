import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_23 : List ℕ := [17, 521, 261, 131, 772, 642, 2626, 403, 4387, 402, 589, 4227, 4232, 2786, 2631, 2308, 85, 153, 773, 643, 1347, 386, 1667]

private theorem valid43_23 : ∀ code ∈ codes43_23, validRelationCode code := by
  decide

private theorem cover43_23 : ∀ q : IncreasingFourTail 41 (⟨23, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_23 (increasingFourValues (N := 43) ⟨⟨23, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a23
    (q : IncreasingFourTail 41 (⟨23, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨23, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_23 _ valid43_23 (cover43_23 q)

end MinModulus.SHCFiveCertificate.Generated
