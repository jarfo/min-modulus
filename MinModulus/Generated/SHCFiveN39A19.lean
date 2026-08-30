import MinModulus.SHCFiveCertificate

namespace MinModulus.SHCFiveCertificate.Generated

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000000

private def codes39_19 : List ℕ := [17, 521, 261, 131, 3785, 2485, 642, 589, 2468, 773, 2631, 4227, 772, 85, 2308, 643, 4884, 771, 402, 465, 2476, 386, 93]

private theorem valid39_19 : ∀ code ∈ codes39_19, validRelationCode code := by
  decide

private theorem cover39_19 : ∀ q : IncreasingFourTail 37 (⟨19, by norm_num⟩ : Fin 34),
    coveredNat 39 codes39_19 (increasingFourValues (N := 39) ⟨⟨19, by norm_num⟩, q⟩) = true := by
  decide

theorem certificate39_a19
    (q : IncreasingFourTail 37 (⟨19, by norm_num⟩ : Fin 34)) : ∃ code,
      validRelationCode code ∧
      relationZeroNat 39 (increasingFourValues (N := 39) ⟨⟨19, by norm_num⟩, q⟩) code = true := by
  exact coveredNat_exists_valid 39 codes39_19 _ valid39_19 (cover39_19 q)

end MinModulus.SHCFiveCertificate.Generated
