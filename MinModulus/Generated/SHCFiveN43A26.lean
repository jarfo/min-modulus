import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes43_26 : List ℕ := [17, 521, 261, 131, 772, 402, 642, 2626, 4227, 2308, 85, 589, 77, 2631, 3911, 153, 773]

private theorem valid43_26 : ∀ code ∈ codes43_26, validRelationCode code := by
  decide

private theorem cover43_26 : ∀ q : IncreasingFourTail 41 (⟨26, by norm_num⟩ : Fin 38),
    coveredNat 43 codes43_26 (increasingFourValues (N := 43) ⟨⟨26, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate43_a26
    (q : IncreasingFourTail 41 (⟨26, by norm_num⟩ : Fin 38)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 43 (increasingFourValues (N := 43) ⟨⟨26, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 43 codes43_26 _ valid43_26 (cover43_26 q)

end MinModulus.SHCFiveCertificate.Generated
