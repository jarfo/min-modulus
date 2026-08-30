import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_20 : List ℕ := [17, 521, 261, 131, 3785, 2485, 4227, 642, 772, 402, 2626, 2308, 4234, 85, 643, 1828, 705, 4884, 770, 773, 153, 2468, 14, 449]

private theorem valid39_20 : ∀ code ∈ codes39_20, validRelationCode code := by
  decide

private theorem cover39_20 : ∀ q : IncreasingFourTail 37 (⟨20, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_20 (increasingFourValues (N := 39) ⟨⟨20, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a20
    (q : IncreasingFourTail 37 (⟨20, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨20, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_20 _ valid39_20 (cover39_20 q)

end MinModulus.SHCFiveCertificate.Generated
